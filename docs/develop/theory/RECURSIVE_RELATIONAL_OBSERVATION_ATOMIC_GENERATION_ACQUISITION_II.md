# 递归关系观察：生成签名与同档案任务取得 II

## 47. Source-bound compressed records for the complete LAB history

**Definition 47.1 (source, task and notation).** The parent of this volume
is [Atomic Generation Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md),
abbreviated AA. Retain its Definition 17.1's LAB, Assumption 20.1's owned
known-alpha initialization and ideal primitive/authority contract,
Definition 20.2's complete frames and replies, Definition 20.4's actual
Next consumer, and Definition 21.1's complete seven-request task $Q_g$.
There is one actually allocated root, with its actual retained binding;
$P_p$ promotes its current alpha leaf and $S_p$ splits its current beta
leaf. There is no deletion, reset, unknown initial source, additional
writer, observable allocation order or independently readable clock.
The source representation, including material unary beta markers, is
AA Definition 17.3's $C(t)$. Logical addresses exclude these markers.

This volume changes only the auxiliary representation of the full local
routing records, from their initialization onward. It does not select a
subword, add a selector or replace $Q_g$ by the marked task of AA §§30–46.
For a successful generation word $w$ ending at $t$, use the existing
$t\in\mathcal D$, $I(t)$, $E(t)$, $W_v(w)$ and $e_b$ of AA §§17–19. Put

$$
\begin{aligned}
x_v&=e_\beta(t_{vL}),&y_v&=e_\alpha(t_{vR}),&n_v&=x_v+y_v,\\
R_v&=\binom{n_v}{x_v},&b_v&=\lceil\log_2 R_v\rceil,\\
\mathcal A(t)&=\{v\in I(t):x_v>0,\ y_v>0\},&a_*(t)&=|\mathcal A(t)|.
\end{aligned}
\tag{AAII.1}
$$

Here $R_v\ge1$, and $b_v=0$ exactly when $R_v=1$, equivalently
$x_vy_v=0$. These counts refer to all successful events, promotions and
splits alike. At a subtree born with type $b$, a traversal counting its
current alpha and beta logical leaves as $a,c$ obtains
$e_b=a+2c-1-\mathbf1_{\{b=\beta\}}$ by AA (AA.73). Thus every count in
(AAII.1) is obtainable from the present bound source, without an endpoint
supplied in advance or an old event archive. Traversal, counters and
arithmetic are paid operations, not additional primitive readouts.

For $W\in\{L,R\}^n$ with $x$ occurrences of $L$, write their positions as
$j_1<\cdots<j_x$, and use the classical constant-weight coordinate

$$
\operatorname{colex}(W)=\sum_{i=1}^x\binom{j_i-1}{i}.
\tag{AAII.2}
$$

The empty sum is zero. Set $r_v=\operatorname{colex}(W_v(w))$.
The mathematical compressed record is the source-indexed tuple of these
ranks; a coordinate of radix one is represented by absence, not a stored
zero. Counts and widths are derived quantities, not persistent banks.

**Definition 47.2 (one installed local layout).** Keep the owned source,
root slot, grants, endpoint connections and finite work arena of AA
Assumption 20.1. Each physical source vertex has its one auxiliary
header-reference slot, initialized null. The three source-edge fields
remain parent, left and right. These auxiliary slots do not enter bare
source support or terminal boundary.

At a branch $v\in\mathcal A(t)$ its slot binds one actually allocated
header with head and tail references, and the header binds a list of
exactly $b_v$ cells. Each cell has one bit and one next reference. From
head to tail the bits are the big-endian, zero-padded $b_v$-bit expansion
of $r_v$. The last next reference is null. The header has no count,
radix, width, address, timestamp, allocation ordinal or cached history.
Every branch outside $\mathcal A(t)$ has a null slot, with no header
and no payload cells for that coordinate. Nonbranches, including unary
markers, also have null slots. The source's already present slot is
still material even when null.

All these bindings and the read/write rights are real owned objects.
A description of their contents does not manufacture authority. The
program is one fixed finite instruction description for all schedules;
its unbounded integers and lists have actual finite backing. The initial
allocated alpha has no record header or cell. No literal routing tape,
literal event journal, persistent coefficient table or complete-history
copy is maintained alongside these records.

At Ready the root cursor, input/request fields, pending operation,
output and scratch contents satisfy the returned domain of AA Definition
20.2, using the present local layout in place of literal tapes. There
is no unfinished source edit, rank rewrite or reserved-material transfer.
The owned work arena and its cleared capacity, if retained for reuse,
remain material and are counted separately from live persistent records.
The model admits each stated finite operation with sufficient finite
fresh material and workspace, as in AA Assumption 20.1; it exposes no
allocation-failure reply or capacity meter.

**Theorem 47.3 (full-history coordinates and their local append law).**
For every finite actual LAB word $w$, the installed contents prescribed
by Definition 47.2 have exactly the same full-history meaning as AA
Definition 19.1's literal tapes. At a fixed reachable source $t$, their
possible contents are in bijection with all $\mathcal H(t)$, with
conditional alphabet size $F_{PS}(t)$ of AA (AA.74). No complete history,
including a promotion, is discarded by omitting radix-one coordinates.

If one actual event occurs strictly below $v$, let $x=x_v$, $y=y_v$,
$n=x+y$, $r=r_v$ just before it, and let $d$ be its first side below $v$.
The new coordinate is

$$
\begin{array}{c|ccc}
d&x'&y'&r'\\ \hline
L&x+1&y&r+\binom n{x+1}\\
R&x&y+1&r
\end{array}
\tag{AAII.3}
$$

Every other existing coordinate is unchanged. A split at $p$ creates
its own empty, radix-one coordinate, with null slot. Each existing
coordinate's radix and bit width are nondecreasing along actual growth;
its header, once allocated, never becomes unnecessary.

Proof. The enumerative ingredient is supplied by Cover, *Enumerative
Source Encoding*, Propositions 1–2, the inverse algorithm and the
constant-weight Example 2, with coordinates read in reverse order.
In the convention (AAII.2), words of length $n$ and left multiplicity
$x$ correspond bijectively to integers $0\le r<\binom nx$.
For completeness of the convention, the last-$R$ block has size
$\binom{n-1}x$ and retains its shorter word's rank; the last-$L$ block
has size $\binom{n-1}{x-1}$ and adds the preceding block size.
Pascal's identity partitions the valid interval, with zero-size blocks
allowed. The empty word is the unique base. This is the credited
counted-block argument, not a new general enumeration theorem.

AA Theorem 19.2 supplies the source-specific bijection between
$\mathcal H(t)$ and the product of the constant-weight word sets.
Composing its coordinates with this classical bijection gives exactly
the asserted contents and alphabet. If $x=0$ or $y=0$, its word is
forced to be $R^y$ or $L^x$, respectively. Both zero gives the empty
word. Its absent coordinate is therefore reconstructed from the source,
without choosing between distinct histories. Conversely a nontrivial
coordinate cannot be suppressed while holding the source and all other
coordinates fixed, by AA Theorem 19.2's independent product.

Appending $R$ changes none of the left positions in (AAII.2). Appending
$L$ adds its new position $n+1$ as the $(x+1)$st left occurrence and
therefore adds $\binom n{x+1}$. The actual-event projection identity of
AA Theorem 19.2 says that precisely these side appends occur at the
proper logical ancestors, for either kind of event. This proves
(AAII.3), including zero child counts and $n=0$.

Appending one fixed symbol injects the old constant-weight word set
into the new one. Equivalently Pascal gives
$\binom{n+1}{x+1}\ge\binom nx$ and
$\binom{n+1}x\ge\binom nx$. Thus $R'$ and $b'$ do not decrease.
A nontrivial coordinate has both counts positive, and growth does not
reduce either. Its header can consequently be retained permanently,
and new cells are needed only for a positive width increment. $\square$

## 48. Acquired counts, finite arithmetic and indexed use

**Definition 48.1 (counting and arithmetic routines).** At a bound logical
subtree root, perform a depth-first traversal of logical source edges,
counting alpha and beta leaves in backed binary counters. Arity tests
recognize the material unary marker as beta and do not descend into it
as a logical child. A previous/current reference pair, the traversal
root reference and parent links suffice to return along the finite
subtree: on first entry visit its left child if it is a branch, on
return from left visit right, and on return from right go to parent;
stop at completion of the designated root. Thus no list of all source
addresses or leaf identities is required. Every read, reference
comparison and counter operation is charged.

For a needed $\binom uk$, return zero when $k<0$ or $k>u$. Otherwise
replace $k$ by $\min(k,u-k)$ and compute

$$
z_0=1,\qquad z_i=z_{i-1}(u-k+i)/i\quad(1\le i\le k).
\tag{AAII.4}
$$

These are exact divisions; induction gives $z_i=\binom{u-k+i}i$.
A fixed finite binary-string multiplication/division routine implements
them using charged buffers. Compute $b=\lceil\log_2 R\rceil$ as the
least nonnegative integer with $R\le2^b$, counting its loop and buffer
work; $R=1$ gives $b=0$. No unit-cost unbounded register or coefficient
oracle is installed. The standard Pascal identities used here are
also the pinned mathlib suppliers identified in Definition 52.1.

**Definition 48.2 (one local indexed routing call).** Suppose the current
source traversal has obtained $x,y,n=x+y$, and an acquired positive
index $j\le n$ requests the $j$th side of $W_v$ and its within-side
occurrence number. A forced coordinate returns $(L,j)$ if $y=0$, or
$(R,j)$ if $x=0$, without a record read. The simultaneous-zero case has
no such positive index. Otherwise read exactly the $b_v$ bits from the
actually bound header into a work integer $r$; the stored list remains
intact.

Use work variables $(i,h,z)=(n,x,r)$. At any stage with a valid rank
and $i>0$, compute $C=\binom{i-1}h$. If $z<C$, the last symbol of this
work word is $R$; replace $(i,h,z)$ by $(i-1,h,z)$. Otherwise its last
symbol is $L$; replace it by $(i-1,h-1,z-C)$. First perform these steps
only while $i>j$. At $i=j$, use the same comparison to determine its
last symbol $d$, but return its occurrence number as

$$
(d,q)=
\begin{cases}
(L,h),&z\ge\binom{j-1}h,\\
(R,j-h),&z<\binom{j-1}h.
\end{cases}
\tag{AAII.5}
$$

This need not materialize the whole local word or a complete history.
All counts, the residual rank, index and comparison operands remain
backed work. Valid installed coordinates alone are its domain; storage
corruption does not add a new request/default to the original service.

**Theorem 48.3 (actual indexed FetchGrowth without literal tapes).**
At any Ready cut satisfying Definition 47.2, a finite paid procedure
using only the retained source, its bound local headers and the actually
received $U(k)$ returns exactly AA Theorem 19.2's indexed event, including
OutOfRange at $k=0$ or beyond the complete current event count. It
preserves all persistent source and record contents. Every descent
uses an actual child and returns the literal event kind and full logical
address, rather than a code for that address.

Proof. The last-symbol block partition used in Theorem 47.3 proves that
each peeling step of Definition 48.2 removes exactly the last symbol
of its valid work word. The residual rank is valid in the indicated
shorter constant-weight set. Empty blocks cause no ambiguity: a
zero last-$R$ block forces $L$, and a zero last-$L$ block forces $R$.
The decreasing nonnegative $i$ makes every requested peel finite.
At $i=j$, exactly $h$ left symbols occur in that first-$j$ prefix.
Consequently (AAII.5) is its actual last symbol and its actual within-side
count. A chosen side has a positive count at most its total multiplicity.
This also proves the forced-coordinate clauses.

Start at the bound root with its acquired $U(k)$ and an empty accumulated
address. Compute $N=e_\alpha(t)$ from a real traversal. To reject zero or
$k>N$, compare a decreasing work copy of $N$ with the actual unary
index marks, stopping as soon as an $(N+1)$st mark is found. This needs
no binary integer of width $\log k$ on an arbitrarily long out-of-range
request. In range, a backed binary index has value $k\le N$; the original
input backing and marks remain paid until cleanup. At a present subtree
root $p$, its birth type is AA (AA.66).
Its forced local prefix is empty, $P_p$, $S_p$, or $P_pS_p$, according
to that birth type and its present constructor, exactly as in AA
Theorem 19.2. If the requested index falls in that prefix, construct
the corresponding literal event and acquired accumulated address.
Otherwise subtract the prefix length. The subtree is a branch, and
its remaining index $j$ lies in $1,\ldots,x_p+y_p$. Obtain the two
counts from its actual child subtrees and use Definition 48.2.
Descend to the actual child $d$ with the returned within-side index
$q$, append $d$ to the backed address, and repeat.

This is exactly the child-shuffle recursion of AA Theorem 19.2, with
its tape scan replaced by its equal indexed side/occurrence result.
Each descent goes to a smaller current logical subtree. Its new index
is in that child's event range, so a nonexistent edge is never
followed. Termination and the correct literal event follow by induction
on the current finite subtree. The work copy and backed address supply
the real Recall payload; there is no unbound external answer provider.
Nothing in this construction writes the retained ranks or the source.
Cleaning its scratch after output preserves the same Ready record.
$\square$

**Definition 48.4 (preflight, source edit and local maintenance).** For an
enabled event at a current leaf $p$, keep the actual event kind, acquired
address, target reference and source binding in pending backing.
Before editing, walk its $d=|p|$ proper logical ancestors. At each,
compare the traversed child's reference to the actual left/right links
to obtain $d_v\in\{L,R\}$. Count its current child events by Definition
48.1 and compute $R,b,R',b'$ from the old counts and that one side
increment. Add $b'-b$ to a reserved-cell total and add one to a
reserved-header total precisely when $R=1<R'$. No rank is needed for
this reservation calculation. Discard a local arithmetic work result
after its total has been backed. Return to the target before editing.

Reserve supplies exactly these additional record cells and headers,
together with the one or two source vertices for the original $P/S$
source template. Reserved objects have actual references, rights and
pending list links; their links and initialization are charged. No
finite-capacity or failure branch is added. Source editing is exactly
AA Definition 20.2: promote by attaching one terminal left marker, or
split by reusing the old unary marker as the left beta root, adding its
marker and a right alpha root. Initialize every fresh auxiliary slot
null; the split root's new coordinate remains null.

After this one source edit, walk the same ancestor chain. At each
ancestor compute the new child counts $(x',y')$ from the actual current
source. The old counts are exactly $(x'-1,y')$ on side $L$ and
$(x',y'-1)$ on side $R$. They are nonnegative. Compute the old width
from these old counts, and read that many old bits from this ancestor's
bound header, or take rank zero when its old radix is one. Apply
(AAII.3). If the new width is positive, bind a reserved header if none
was previously needed and extend its list by exactly $b'-b$ reserved
cells. Overwrite the list with the new zero-padded $b'$-bit rank.
Previously allocated cells are reused in place. Pending subphases keep
the current header, remaining input/output bits and any not-yet-linked
cells explicit. No service call is admitted during this maintenance.

No list of all ancestor plans is retained. Preflight and maintenance
may recount subtrees and recompute coefficients. Once an ancestor has
been updated, its source counts are still the same new counts; record
writes do not change the source-edge projection. The old counts of an
ancestor not yet updated are therefore still obtained by the stated
single decrement. At the last ancestor all reserved record material
has been attached. BuildAnswer, Print, End, the supplied local ACK,
root Return and scratch clearing/reuse then follow AA Definition 20.2.

## 49. The unchanged seven-request service on the same bound source

**Theorem 49.1 (causal installation and complete returned-service
correspondence).** Under AA Assumption 20.1 with Definition 47.2's one
local layout, Definitions 48.1–48.4 give one source-independent finite
driver with the following properties for every finite supplied sequence
of complete request frames.

1. At each returned Ready the actual successful word $w$, the actual
   bound source $t$ and the compressed record satisfy Definition 47.2
   and Theorem 47.3, beginning with the allocated alpha and empty record.
   Every finite legal LAB generation word is attainable.
2. All seven original request kinds retain their complete guards,
   refusal and OutOfRange behavior, request framing, reply tags and
   payloads. Every completed request has real finite output, End,
   local acknowledgement and Return to that same bound root. A proper
   unsupplied frame prefix waits with its actual acquired pending data.
3. In-range FetchGrowth returns the same complete old event as the
   original service. In-range Next consumes that actual acquired result,
   performs its original current left descent on the same live source,
   executes the resulting genuinely enabled $P/S$, and returns the
   original two-event payload. Its settled source and full-history
   successor correspond to the original service's successors.
4. The correspondence holds after every prefix of any finite request
   sequence, including refused operations, arbitrary mixtures of all
   seven kinds and requests chosen from already returned replies.

This is correspondence of the declared semantic service, not equality
of primitive work, allocation names, busy-state encodings or duration.
The represented successful-history domain is exactly the original
$\mathcal H(t)$, without an extra scheduling restriction.

Proof. Initially the actual alpha root has no events or coordinates,
and all its source and auxiliary fields have the required initialized
values. The source-independent parser and receive-latch argument of AA
Theorem 20.3 applies verbatim: each received bit is backed before its
latch is cleared; each address/index length mark really exists; and
only a complete frame enables its handler. Preserve the original seven
three-bit tags, the unused BadFrame tag, $A(p)=1^{|p|}0p$ and
$U(k)=1^k0$, and all eight three-bit reply tags and their original
payloads. Compression introduces no new external frame, bit field,
response or acknowledgement dependency.

Tag, HasPromotion and HasSplit read exactly the same current source
and AA (AA.67). Absent addresses, branches and wrong-type targets give
the original tagged refusal for addressed growth, without a source or
record change. Missing authority or a wrong controller phase disables
the same primitive; it is not converted into a new reply. Queries and
BadFrame preserve $w$ and its compressed record. Finite address
navigation uses the actual links and arity tests, including the unary
marker rule, exactly as in AA §20. Their reply backing therefore has
the same literal content as before.

For an enabled addressed growth, the preflight chain has exactly the
$d$ proper logical ancestors of its actual target. Every child count
is obtained by a finite current-source traversal. Equation (AAII.3)
and Theorem 47.3 give finite nonnegative material increments. Reserve
obtains that actual material under the unchanged sufficient-material
premise. Preflight changes neither source nor records. The local source
template then performs exactly the original single $P_p$ or $S_p$.
Parent bindings persist, including the marker reused at a split.

For each proper ancestor the new source differs in its indicated child
by precisely that one successful event. AA (AA.73) and Theorem 19.2's
projection identity therefore make its post-counts the old counts plus
that one side increment. Hence Definition 48.4 recovers the true old
counts even after the source edit. Ancestors already maintained do not
change these counts. At an unmaintained ancestor the old stored rank
is still the old word's rank by the induction invariant. Its old
width is reconstructed before reading; a forced old word needs no
header. Applying (AAII.3), extending to the computed new width and
writing all its bits gives exactly the actual newly appended local
word. An untouched coordinate and the split root's new empty coordinate
already have their required contents. The preflight sums match precisely
the consumed increments, so no unattached reservation remains when
maintenance completes. All old live record cells remain in use; none
is left as an obsolete retained rank version.

Finite subtree traversals terminate by their finite edge tours;
coefficient and binary routines have finite loop ranges; ancestor walks
terminate at the bound root. A pending rank rewrite is not a Ready
cut and cannot be read as a finished record. Thus this completes an
actual, causal record update before constructing the Growth reply.
The only appended event is the one genuinely executed, so every earlier
indexed event is preserved and the new last one is callable.

For FetchGrowth, Theorem 48.3 supplies its actual in-range event or
OutOfRange, including zero. For Next, retain that handler's work result,
index and continuation phase without an outer Return, as AA Definition
20.4 requires. An OutOfRange result gives the same no-growth reply.
Otherwise its historical address is still a logical source position
because LAB has no deletion. Navigate from the retained real root to
that position and follow current logical left children through branches.
The finite descent reaches a current alpha or beta leaf. Its tag
chooses exactly the original enabled promotion or split, with the same
real target and authority. Apply the already proved source/record
transaction to that event. Construct the reply from the retained old
event and this actual new event, not from a separately replayed source.
This is precisely AA Theorem 20.5's source successor and successful-word
extension; only the internal representation of that word differs.

Every handler seals a finite answer backing, traverses it to Print its
specified bits and End, takes the supplied local ACK, returns to the
same root and clears/reuses its pending and scratch fields. These are
actual finite edges under AA Assumption 20.1; no eventual external ACK
is postulated. This proves return and restores the invariant.

Induct on completed requests. Each case gives the original complete
reply and corresponding successor, so the invariant and correspondence
hold at every prefix. The same induction covers a controller choosing
its next frame from the common reply prefix. Supply addressed $P/S$
frames for any desired legal finite generation word; the original
guards accept each event by AA Theorem 17.2, and the finite transaction
adds no scheduling prohibition. Conversely every successful edit is
one original guarded LAB event. Thus no complete original histories
are lost or new illegal ones admitted. Partial received frames retain
only their received prefix and pending parser state; a finite supplied
completion resumes the proof. $\square$

**Theorem 49.2 (exact task relation, including semantic successors).**
At fixed initialization, source binding and current rights, relate a
literal-tape Ready state $(t,\mathcal W)$ of AA §20 to the compressed
Ready state $(t,\mathcal R)$ precisely when every local rank of
$\mathcal R$ encodes that actual $W_v$. This relation is total in both
directions on their actual semantic images. Each original framed request
has the same legality/refusal and reply in related states, and its
settled successors are related. Consequently the full $Q_g$ task kernel
for the compressed record is exactly equality of the complete successful
word $w$, with its source interpretation. The relation preserves complete
finite continuations, including actual Next successors.

Proof. AA Theorem 19.2 and Theorem 47.3 give inverse coordinate maps
on every fixed reachable source, hence the image relation is total and
single-valued on contents. Theorem 49.1 proves each request case, with
its actual resulting source and updated represented word. This includes
the source edit chosen by the acquired old event during Next. Induction
composes the relation for any finite legal request sequence.

Equal represented words give the same source, guards, indexed events
and current Next leaves. Conversely two different words differ at a
first indexed event, or one is a proper prefix. FetchGrowth returns
distinct literal events at that index, or an event versus OutOfRange.
It therefore separates those states by an original request. This is the
existing full-task kernel argument of AA Theorem 21.2, now with its
concrete acquired compressed operands and maintained successors.
$\square$

## 50. Selected persistent material and an unbounded ambiguous family

**Definition 50.1 (material coordinates and complete charging).** On one
actual run, let $P,S,N,D,V$ retain AA (AA.77)–(AA.78)'s meanings, including
events chosen by Next. Set

$$
B(t)=\sum_{v\in I(t)}b_v,\qquad H(t)=a_*(t).
\tag{AAII.6}
$$

A located reference field is one field occurrence, including a null
field; its actual bit representation is charged separately. The selected
persistent material comprises the physical source vertices, source-edge
fields, their auxiliary slots, live local headers and live rank cells.
It excludes neither source vertices nor their null auxiliary slots.
It excludes the separately itemized installed program, endpoint/root
registers, current grants, work arena, request/answer backing and work
registers from this particular tally, not from the process or its cost.

Complete charging on the same run retains AA Definition 22.3's actual
input/output lengths, navigation, source allocations, authority/grant
operations, tests, printing, ACK, Return and clearing/reuse. It adds every
source counting tour, binary-counter update, binomial multiplication and
exact division, width calculation, rank read/copy/rewrite, preflight
walk, reservation and link initialization. It charges the retained input
marks even for an arbitrarily large out-of-range $k$. Reference values
are never unit-width integers, and a cleared reusable work buffer still
occupies its retained capacity.

**Theorem 50.2 (exact live material of this layout).** After any finite
completed request sequence, the selected persistent material of Definition
50.1 has exactly

$$
\begin{array}{c|c}
\text{material}&\text{number}\\ \hline
\text{physical source vertices}&V=1+P+2S\\
\text{source-edge reference fields}&3V\\
\text{source auxiliary reference slots}&V\\
\text{local record headers}&H(t)\\
\text{header reference fields}&2H(t)\\
\text{rank cells and their bit payload}&B(t)\text{ cells and }B(t)\text{ bits}\\
\text{rank-cell next fields}&B(t)
\end{array}
\tag{AAII.7}
$$

In particular there is no persistent record header, payload, length or
count for a radix-one coordinate. All live record cells and headers
allocated earlier are included in (AAII.7). There is no uncounted obsolete
rank version. In the same located-field convention the original literal
layout has $S$ headers and $D$ tape cells, by AA Proposition 22.1, with
the same source contribution. Here

$$
\log_2 F_{PS}(t)\ \le B(t)
<\log_2 F_{PS}(t)+H(t)\quad\text{if }H(t)>0;
\qquad B(t)=0\text{ if }H(t)=0.
\tag{AAII.8}
$$

These are attained live persistent-material and conditional payload
statements for this layout, not whole-resource or global-bit optima.

Proof. The source uses exactly the original templates, so its vertex
count and three initialized source fields per vertex are AA Proposition
22.1's counts. Definition 47.2 initializes one auxiliary slot at every
physical vertex. The invariant of Theorem 49.1 has exactly one bound
two-reference header at every currently nontrivial coordinate and none
else. Its bit list has exactly that coordinate's current $b_v$ cells,
each with one next reference. This proves the present counts.

Theorem 47.3 makes both active membership and widths nondecreasing.
A transaction allocates exactly the missing headers and positive width
increments, reuses all old cells and retains no superseded header or
cell. Thus the present counts also include all earlier record allocations
in this layout. Source markers that later become logical roots keep their
existing source fields and slot; no duplicate source object is inserted
for that role change. Reserved but not yet attached objects exist only
in busy phases and are charged there.

For $R_v>1$, $\log_2R_v\le b_v<\log_2R_v+1$; for $R_v=1$ both are zero.
Summing and using AA (AA.74) proves (AAII.8). The lower inequality is
the already supplied full-history conditional alphabet bound, not a
new total-material converse. $\square$

**Theorem 50.3 (coexistence and finite work, without free arithmetic).**
The driver of Theorem 49.1 can perform each transaction with the source
and all live records retained throughout. Preflight needs no array of
ancestor plans or persistent count cache. If $N_+$ is the event count
after a proposed successful edit, the compressed arithmetic backend
needs $O(N_++1)$ temporary binary bit positions and a constant number of
reference-register roots, in addition to actual request/answer/address backing, the
original receive/index marks, reserved fresh material and retained work
capacity. Every such operation has finite explicitly charged work.
No bound on arbitrary request sizes, output volume or whole-run work
is inferred from $N_+$ alone. For a query or refusal set $N_+=N$.
Backing objects and links for the temporary bit positions, and all
actual reference widths, are additional charged material; the bit-position
bound is not a bound on their complete binary encoding.

Proof. Current logical depth is at most the split count and hence at
most $N_+$. Each subtree event count and local word length is at most
$N_+$. Every binomial queried for a local coordinate, update or valid
peeling step is at most $2^{N_+}$. Formula (AAII.4)'s partial binomials
are nondecreasing up to the queried coefficient, and its multiplication
numerator is at most that coefficient times $N_++1$. A constant number
of binary integer buffers, including schoolbook multiplication/division
scratch, therefore has $O(N_++1)$ bits. Count, width and peeling-loop
indices fit this bound as well. Bound $B\le\sum_v n_v=D\le N_+^2$,
using at most $N_+$ ancestors per event, so the two preflight material
totals need only $O(\log(N_++2))$ bits.

Counting traversals use the fixed number of source reference registers
of Definition 48.1, with no retained address enumeration. Walk the
ancestor chain once for preflight and once for maintenance, retaining
only the next ancestor/child references and the current local arithmetic
work. Recompute its counts at each visit. Header/cell allocation totals
are determined before editing. A pending pool can give each reserved
record cell its already needed next field and each reserved header its
head field as temporary pool links; these actual writes and roots are
charged. As the pool is consumed, initialize each final field and attach
its object. This requires no separate persistent pool-cell archive.
All source, old record, fresh reservation and current arithmetic work
coexist until their respective attachments/rewrites finish.

At a rank rewrite retain a work copy of the new rank while its actual
$b'$ bits are written into the bound cells; a work residual can emit
these bits by a finite binary scan. Header tails and cell links are
actual writes, not implicit arrays. At a local routing call, peeling
needs only a constant number of these integer buffers and the acquired
index, rather than an $n$-symbol decoded tape. Discard local buffers
before the next ancestor or child, using the declared clearing/reuse
operations. Global event counts used in this proof are bounds, not
extra runtime inputs or free stored counters.

For an arbitrarily large out-of-range unary request, use the bounded
mark comparison in Theorem 48.3 before creating any in-range arithmetic
index. Thus its original received backing can be arbitrarily large,
while this particular additional binary-index work stays within the
stated backend bound. In-range work indices never exceed the actual
current event count.

For a successful event at depth $d$, choose the displayed routines to
count both child subtrees on every visit, including zero-event children.
There are exactly $d$ preflight and $d$ maintenance ancestor visits and
$4d$ child-counting tours. Computing old and new radices uses $4d$
binomial queries across those visits; the append offsets add one more
query at each ancestor whose actual side is $L$, hence at most $d$.
Width calculations, reads of the old bit lists, writes of the new bit
lists and material-pool operations are additional. This is a located
contribution, not a total bit-operation tariff. Each counting tour
traverses an actual finite subtree; no tour or coefficient query is
replaced by a free persistent count field.

There are finitely many source vertices, ancestors, bit cells and
coefficient iterations on each completed finite request. Formula
(AAII.4) uses at most $N_+$ exact multiplications and divisions per
coefficient query; binary routines of finite input length terminate.
The full Fetch descent is finite by Theorem 48.3. These facts prove
finite work with every such operation charged; they assert neither
unit-time arithmetic nor the original literal driver's tariff.

The acquired original request, its marks and pending latch exist while
this backend runs. Its output backing then coexists with the updated
source/records and the retained operands needed to construct the full
reply. Print and its cursor coexist with that backing until ACK and
Return permit cleanup. The program, source bindings, grants and every
reference value are present throughout. A missing right, a supplied
incomplete input, insufficient finite material, crash or interruption
is outside the same completion premise as AA §20, rather than an
unpriced completed request. $\square$

**Theorem 50.4 (quadratic literal retention versus compressed order
$m\log m$ on genuinely ambiguous reachable sources).** Define finite
terms by

$$
u_0=\beta,\qquad u_{m+1}=\langle u_m,\beta\rangle.
\tag{AAII.9}
$$

For every $m\ge2$, the known-alpha installation reaches $u_m$; its
complete-history fibre is ambiguous. Every history in that fibre has

$$
\begin{aligned}
S&=m,&P&=m+1,&N&=2m+1,&V&=3m+2,\\
D&=m^2,&F_{PS}(u_m)&=\prod_{j=1}^m(2j-1),\\
H(u_m)&=m-1,&B(u_m)&=\sum_{j=2}^m\lceil\log_2(2j-1)\rceil
                       =\Theta(m\log(m+1)).
\end{aligned}
\tag{AAII.10}
$$

Thus the literal local layout retains exactly $m^2$ side cells and $m$
headers; the installed compressed layout retains $B(u_m)$ rank cells
and $m-1$ headers. Including the common source, their selected persistent
object counts are respectively $\Theta(m^2)$ and
$\Theta(m\log(m+1))$. Their located-reference-field counts have those
same orders. The saving does not depend on all coordinates being forced:
there are $m-1$ genuinely nontrivial coordinates.

Proof. A nested sequence of finite legal words is

$$
h_m=P_\varepsilon\,
       \prod_{i=0}^{m-1}\bigl(S_{L^i}P_{L^iR}\bigr).
\tag{AAII.11}
$$

After $P_\varepsilon$ the source is $u_0$. Its deepest left beta leaf
is at $L^m$ in $u_m$. Splitting it and then promoting its new right
alpha creates the next all-beta left comb $u_{m+1}$, proving the
endpoint assertion and legality of every displayed prefix. These are
finite actual service executions by Theorem 49.1. Their nested
combinatorial description assumes no physically completed infinite
supply of material or input.

The branches are $L^i$, $0\le i<m$. A subtree with $j$ remaining
branches has left subtree $u_{j-1}$ born beta and right subtree beta
born alpha. The former has $j$ beta leaves and no alpha leaf, so AA
(AA.73) gives $x=2j-2$. The latter gives $y=1$. Thus its local length
is $2j-1$ and its radix is $2j-1$, including the bottom radix one.
Summing local lengths counts each actual event once for each proper
ancestor, exactly as in AA Proposition 22.1. Therefore
$D=\sum_{j=1}^m(2j-1)=m^2$. Multiplying local radices gives the
displayed $F_{PS}$ by AA Theorem 19.2, and it is greater than one for
$m\ge2$. There is a separate conditional history choice at every
$j\ge2$, not just one isolated witness.

There are $m+1$ beta leaves and no alpha leaves. AA (AA.78) gives
$P,S,N,V$. The nontrivial branch count and total rank width follow
from the local lengths and radices. The width sum is at most
$m(\log_2(2m-1)+1)$. For $m\ge4$, at least $\lfloor m/2\rfloor$
indices have $2j-1\ge m-1$, so the sum is at least
$\lfloor m/2\rfloor\log_2(m-1)$. This proves its order.
The exact material theorem now gives the object and field orders,
with the common linear source retained in both. $\square$

**Definition 50.5 (meaning of the retention comparison).** The word
“material” in Theorem 50.4 counts the explicitly displayed objects,
bit payload positions and located reference-field occurrences. It is
not a fixed-width encoding convention for reference values. For an
actual implementation let $\lambda(f)$ be the number of bits used by
each retained reference field $f$, and include the corresponding sums
$\sum_f\lambda(f)$, object descriptors, rights, allocator and work-arena
metadata in its full storage. Neither those widths nor an implementation's
address space are set to one bit here. In particular choosing reference
widths of logarithmic order can add another logarithmic factor to the
compressed bit count; (AAII.10) does not assert a global
$\Theta(m\log m)$ bit bound.

On the finite path (AAII.11), every local radix at every preflight,
maintenance or valid peeling stage is at most $2m+1$: completed sources
have $y=1$, and the intervening newly split branch has $y=0$ until its
right promotion; the ancestors still have their single right promotion.
The arithmetic buffers of (AAII.4) can consequently use
$O(\log(m+2))$ bits on these paths, since their numerators are at most
$(2m+1)(2m+2)$. The maximum addressed request and Growth payload have
$O(m+1)$ bits, as do their explicit length marks. This identifies
concrete simultaneously charged work/output contributions on the
witness paths; it does not bound an arbitrary later request with an
unbounded unary index or a long sequence of repeated queries.

Global mixed-radix packing remains a valid finite storage/work alternative
for the product in AA (AA.74), as already observed after AA Theorem 19.2.
It is not installed in Definitions 47.2 and 48.4. A global implementation
would have to supply its actual backing, source-dependent radix
calculations, update/unpacking work, bindings, output and return. Its
material comparison can involve header placement, reference fields,
working versions and traversal as well as integer rounding; it is not
settled by subtracting two rounded payload lengths. No impossibility,
dominance or optimum for that alternative follows from the local
construction or the comb family.

## 51. Independent expressions and the exact recovered domain

**Definition 51.1 (four expressions at returned cuts).** Fix the initialized
root binding, service entry, grants and Ready domain of Definition 47.2.
Bare source space $S_0$ is the oriented support of actual source edges;
bare source boundary $B_0$ is their actual terminal-address antichain,
including the unary-marker distinction, as in AA Definition 17.3.
The local compressed annotations $\mathcal R$ consist only of the
source-located live rank contents and their absent-coordinate convention.
Define

$$
S_r=(S_0,\mathcal R),\qquad B_r=(B_0,\mathcal R).
\tag{AAII.12}
$$

These annotations are actual local branch records, not an unrestricted
copy of input, output or controller chronology. Time $T_g$ is the
complete actual successful $P/S$ word, as in AA Definition 21.1;
its causal membership order is the separately defined $T_c$. Memory
$M_r$ is the retained source and live local record backing with its
currently callable seven-request driver and rights. Raw unused object
names and obsolete scratch contents are not semantic readouts.

**Theorem 51.2 (common-source recovery and operation agreement).** On
this actual Ready domain, $S_r,B_r,T_g,M_r$ each determine exactly the
full $Q_g$ task state. Their mathematical recovery maps are mutually
inverse on their actual images, agree along all routes and commute
with every legal completed request, its entire reply and its semantic
source/record successor. The bare $S_0,B_0,T_c$, even supplemented by
complete split chronology, retain AA §18's full-order ambiguities.
No recovery of complete controller chronology or arbitrary busy states
is asserted.

Proof. Source-edge support and the terminal antichain interconvert
by AA Definition 17.3, preserving the unary beta marker; either
recovers the same $t$. Its actual annotations are decoded using
(AAII.1) and Theorem 47.3 into exactly AA's local routing words.
AA Theorem 19.2 then reconstructs the single actual $w$. Conversely
that $w$, from the known alpha, determines $t$ and all its projected
local words; (AAII.2) gives the exact rank annotations and absence
positions. Reading $M_r$'s owned backing obtains these same data, and
its callable interpretation is Theorem 49.1. Reconstructing their
mathematical descriptions is not a new allocation of rights or a
claim that arbitrary externally supplied codes can install a service.

Each round trip uses the same reconstructed word and source, so it
returns the original view on its actual image. Every composed recovery
route therefore agrees. Theorem 49.2 supplies full request and successor
agreement, not only a static content bijection. A growth appends its
actual event to $w$ and updates precisely its ancestor coordinates;
Next first decodes its actual old event and then appends the same
current-source event on either route. Queries and refusals leave this
word unchanged. Finite-request induction proves the claimed commutation
and the exact kernel for every view.

None of these arguments puts ranks into bare $S_0$ or $B_0$.
AA Theorem 18.2's exact split-erasure fibres and Theorem 18.3's
criterion remain unchanged, as does AA (AA.75)'s actual differing
Next-successor witness. Source plus an unrecorded serial choice still
cannot supply the missing rank. Finally an extra completed Tag request
changes complete input/output/controller chronology without changing
$w,t,\mathcal R$. During Receive its partial input and during Maintain
its pending old/new rank and ancestor cursor affect the next lawful
primitive action. These data are neither settled word nor bare geometry.
Compression therefore preserves the old distinction between successful
generation time and complete controller chronology, and the Ready
restriction is essential. $\square$

## 52. Supplier subtraction and preserved mathematical boundaries

**Definition 52.1 (precise correspondence).** The installed local layout,
its acquired count/rank transaction with omitted forced headers, its
complete original-service correspondence and the ambiguous comb material
family are `repo-derived` synthesis on the declared LAB process. Their
intermediate counting and enumeration methods have the following exact
suppliers; they are not proposed as new general coding or quotient theorems.

| Supplier | Reused content and correspondence; remaining distinction |
| --- | --- |
| [AA §§17–23](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction) | The exact birth-typed source domain, every legal history as an extension, the product of full local shuffles, known-alpha ownership, acquired frames, live Fetch/Next, ACK/Return, exact full-task kernel and literal source/tape/journal counts are reused. The paragraph after Theorem 19.2 already supplies the static colex and mixed-radix possibilities and expressly does not install them. The new obligations are source-derived paid counts, one concrete growing local rank layout, causal overwrite/extension, live indexed consumption and the attained material family. |
| [AA §29](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#29-exact-supplier-overlap-and-remaining-domains) | Its attribution to Grossi–Gupta–Vitter, *High-Order Entropy-Compressed Text Indexes*, §4.2, Lemma 4.2/Figure 2, and their rank/select suppliers is retained. Local binary routing and within-side navigation are established methods. Here the paid peeling routine supplies no constant-time succinct rank/select bound. Identity-selected handoff and adaptive marked records are different tasks and are not substituted for complete $Q_g$. |
| [AA §37](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#37-a-supplied-address-presentation-and-exact-frontier-thresholds) | Finite source traversal computes current leaf counts with specified address/birth semantics. Its exact counter-path lifting and Petri coverability decision concern finitely presented selection controls, not these full-history coordinates. No new selector, threshold computation or identification of source with leaf counts is used here. |
| [NCR Theorem 8.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md#8-independent-command-choices-require-an-acquired-order-relation) | Causally acquired enumerative complements, histogram-relative capacity, finite paid unrank/append/rerank and full historical-row lookup already exist for its separate Native command ingress. They do not give LAB's branch attachment or its source-selected actual Next successor. This volume claims neither first online ranking nor a new general chronology complement. |
| [Spatial Records Chronology §§19–20](RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md#19-one-causally-updated-rank-and-actual-image-recovery) | Causal counted-block updates, actual-image inverse, count-only coefficient arithmetic and explicit distinction between rank bits, original source, temporary buffers and output are reused. Its singleton family does not supply the present infinitely many ambiguous LAB fibres, branch-local absent headers or the seven LAB services. |
| [Recovery Geometry II §§52–58](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md#52-the-authentic-acquired-phase-separates-every-integer-pulse-length) | Length separation and a terminating inverse without old length advice already hold for its authentic integer pulse endpoints, under the earned primitive law and its digit-menu threshold. This volume claims no new general removal of length advice. Its missing local widths are recomputed from the actual finite LAB source by (AA.73), rather than inferred from an affine endpoint or an integer annihilator. The two source/operation contracts are distinct. |
| [Boundary Dynamics §102.4](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md#1024-重复半系数给出的全路径容量与原-stop-解码) and Propositions 102.4–102.6 | Last-coordinate colex blocks, causal arithmetic updates, zero-size block handling and supplementary-alphabet versus full-resource distinctions are supplied for its polynomial-prefix fibres. Its Stop and original-parser conditions are not imported into LAB; no new general colex or singleton-capacity theorem is claimed. |
| [Cover, *Enumerative Source Encoding*, §I Propositions 1–2, inverse algorithm, §II Example 2](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf), [doi:10.1109/TIT.1973.1054929](https://doi.org/10.1109/TIT.1973.1054929) | `literature-attested`: indexing by prefix-block counts and its inverse, including constant-weight words. Reversing coordinates and coding $L$ by one gives (AAII.2); appending $L$ adds its one new binomial term. The paper credits prior constant-weight indexing. This is an arithmetic supplier, not a theorem about actual owned LAB material or complete source successors. |
| Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, [Data/Nat/Choose/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/Choose/Basic.lean) | `Nat.choose`, `choose_succ_succ`, `choose_zero_right`, `choose_self` supply Pascal recursion and the forced-side identities. The namespace and integer inputs correspond directly to the nonnegative binomials above. They do not count constructed objects or charge an integer routine. |
| [NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs) | `term_at_prim`, `readout_prim` and private `treeView`, `child`, `walkStep`, `walk_exact`, `rootReply`, `readout_walk` supply exact finite ordered-tree navigation and blocked-address readout. Their Native leaf representation and global `substitution_prim` are not the material unary-marker LAB edit. The source bridge and rights remain those of AA §20. |
| [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | `sourceControl`, `initialControl`, `native_source_producer` and private `traverse`, `production_reads`, `stationary` already acquire every finite unknown stationary Native tree with real reads and backed finite stacks. This volume starts from the actually allocated known alpha and maintains its own edits; it claims no missing general unknown-tree acquisition theorem or new implementation of Native reads. |
| [EnabledPathSwapConnectivity](../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean), [Scribe](../../../Blueprint/D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.scribe.cs), and [SwapClosureExtensionInvariance](../../../D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.lean), [Scribe](../../../Blueprint/D5/S3/ConceptDynamics/PartialIdentification/SwapClosureExtensionInvariance.scribe.cs) | `result` gives finite-poset enabled executions, extension correspondence and legal exchange connectivity, used through AA Theorem 17.2. `extension_invariance_from_swap_connectivity` gives the generic parent-local invariance composition under its stated hypotheses. Neither is a local rank allocation or acquired full-service theorem; no reproof of their general content is asserted. |

Subtracting static ranking, generic route agreement and ordinary finite
arithmetic leaves the conjunction proved here: absent persistent records
at all forced coordinates; source-paid, future-free growing updates
without discarded retained versions; exact original full-service indexed
use with real source successors; and a non-singleton reachable family
with quadratic versus $m\log m$ selected persistent material. The claim
is this source-relative synthesis, not exhaustive worldwide originality.

**Definition 52.2 (unresolved domains).** The stated completion requires
the original owned known-alpha LAB installation, actual current rights,
no concurrent writer/revocation/crash/interrupt, finite complete supplied
frames, the supplied local acknowledgement and sufficient finite material.
Observable capacity/exhaustion, primitive-duration readouts, allocation
ordinals or a selector reading omitted work state would change the
service task and require new legality/reply/successor proofs. Reference
encoding, physical realization, finite-device limits, arithmetic work
optimization and whole-resource/global-bit optimality remain separate
obligations; no such optimum follows from (AAII.8) or the comb family.

The recovered four expressions use explicit local order annotations at
Ready. They do not invert arbitrary busy states, recover full controller
chronology, obtain lost historical order from bare geometry, acquire an
unknown initial history, create authority from a code or supply one
physically realized infinite run. General physical space/time and a
universal reduction to alpha/beta generation are not established.
Every original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization, terminal and final-no-Ready obligation retains
its exact prior scope. AA §§1–16's original INITIAL interfaces and
AA §§24–46's selected/marked services have not been replaced or solved
by this compressed complete LAB service. The broader common-process
four-expression and parsimony programme remains unresolved beyond this
bounded constructive result.

## 追加锚（本行以下为增补区）

## 53. Unknown entry through the original growth guards alone

**Definition 53.1 (entry source and logical navigation).** Retain AA
Definitions 17.1 and 17.3. An entry is a finite term
$t\in\mathcal D$ on one actual source obtained by a finite legal LAB
word from its originally allocated $\alpha$. Write $\mathcal L(t)$
for all its logical positions, including branches, and $F(t)$ for its
logical leaves. Logical navigation follows a letter only at a binary
branch. A strict logical descendant of either kind of leaf is absent.
In particular, the material left marker of a $\beta$ is not a logical
child or an addressable growth target.

The source object is the persistent rooted oriented material tree
$C(t)$, with the original parent, left and right fields. A successful
$P_p$ retains its target vertex and attaches one fresh left marker.
A successful $S_p$ retains its target as a branch, reuses its old marker
as the left logical $\beta$ root, attaches that vertex's fresh marker,
and attaches a fresh right $\alpha$ root. These are exactly AA
Definition 20.2's source templates. They add respectively one and two
source vertices and delete none. Auxiliary observer records are not
source vertices.

**Assumption 53.2 (authentic guard-only attachment).** One fixed finite
dispatcher implements those two addressed operations on this very root.
Its actual callable reference, original root/address orientation, current
exclusive $P/S$ authority, input/output connections and local return
acknowledgement are supplied. The attaching observer has source-independent
finite instruction code and initially empty source-dependent work records.
It receives neither $t$, its size, an old generation word, old routing
tapes, a terminal roster nor a source-dependent response table. It has no
Tag, Native Read, membership, recall, Next, field, reset or cloning port,
and cannot inspect the dispatcher's private source fields. Only complete
dispatcher replies are source-dependent observations. The bound reference
is opaque; allocation names, elapsed work and resource amounts are not
additional readouts.

Calls and observer updates are serialized. There is no concurrent writer,
revocation, crash, interrupt or autonomous source transition. Each claimed
finite execution has sufficient finite source material, owned code and
work backing, and current rights to their construction and later use.
There is no observable quota or allocation-failure branch. Acquisition,
communication, local computation, allocation, grants, retention and clearing
all have their actual charges; none is a free source observation. Missing
rights or a wrong phase disable the corresponding primitive, rather than
returning a leaf-type refusal.

This is a different minimal installation from AA Assumption 20.1 and
Definition 47.2. It does not construct or maintain their historical routing
records. A producer has really paid for the old finite source preparation,
but its old serial word need not be available to this observer. Removing
those record services here makes no assertion about acquiring their full
seven-request task.

**Definition 53.3 (complete guard task $Q_A$).** On a current term $u$,
the semantic reply and successor of a complete addressed request are:

| Current logical target at $p$ | $P_p$ | $S_p$ |
| --- | --- | --- |
| absent | Refusal(absent), unchanged $u$ | Refusal(absent), unchanged $u$ |
| branch | Refusal(branch), unchanged $u$ | Refusal(branch), unchanged $u$ |
| $\alpha$ | Growth$(P,p)$, replace that leaf by $\beta$ | Refusal(wrong type), unchanged $u$ |
| $\beta$ | Refusal(wrong type), unchanged $u$ | Growth$(S,p)$, replace that leaf by $\langle\beta,\alpha\rangle$ |

Use the original three-bit $P/S$ request tags and
$A(p)=1^{|p|}0p$ of AA Definition 20.2, with the same bit meanings for
$L,R$. Growth has its original three-bit reply tag, kind bit and $A(p)$;
a refusal has its original three-bit tag and two-bit reason. Thus their
lengths are respectively $2|p|+5$ and $5$. To specify the entire minimal
parser, each of the other six three-bit request tags is a complete
unsupported frame and returns the three-bit BadFrame reply, with no
payload and no source change. It does not call an omitted AA service.
A $P/S$ tag followed by a proper incomplete address frame waits for the
missing suffix and has no completed reply. The parser consumes exactly
one frame before return; later input belongs to a later request.

Receive backs each input bit before releasing its pending latch.
Navigate follows logical branches from the retained root. Guard applies
the displayed cases. A successful request reserves its finite fresh
material before the source edit. BuildAnswer seals the entire reply,
Print transmits every bit followed by End, the supplied local
acknowledgement enables Return, and finite scratch cleanup restores Ready.
Return may follow the parent chain from the target to the root. No next
request is admitted during an unfinished edit or reply. The pending
request, cursor, reserved references, answer and phase remain actual busy
state. A source cut used below is settled only after this return and the
observer's corresponding record update.

$Q_A$ compares the same finite future frames, their complete replies,
enabledness and all resulting settled source successors. It exposes no
private observer archive, source allocation names, primitive-duration
trace or arbitrary busy state. Its semantic source equality is equality
of rooted oriented contents with this fixed binding and authority,
disregarding fresh-name spellings. This convention preserves actual
binding relations; it does not identify different authorities or roots.

## 54. A destructive probe acquires both the entry and its real endpoint

**Definition 54.1 (normalization and probe controller).** Define

$$
\nu(\alpha)=\beta,\qquad \nu(\beta)=\beta,\qquad
\nu(\langle v,w\rangle)=\langle\nu(v),\nu(w)\rangle.
\tag{AAII.13}
$$

The following controller uses only actual $P$ calls. Begin with the
empty logical address and an empty traversal stack. At a scheduled
address $p$, transmit the complete $P_p$ frame and consume its complete
returned answer. Growth$(P,p)$ appends an $\alpha$ constructor to the
entry code and a $\beta$ constructor to the current code; this visit is
finished. Refusal(wrong type) appends $\beta$ to both codes and finishes
the visit. Refusal(branch) appends a branch constructor to both codes,
schedules the left child, and retains the pending right-child continuation.
After the left visit it visits that right child. It stops when the root
visit and every retained continuation have finished. No $S$ is issued.

The codes are ordinary preorder words: alpha is $00$, beta is $01$,
and branch is $10$, followed by its left and right code words. The
unused symbol $11$ is invalid. Decoding starts with one pending subtree
slot; a leaf fills one slot and a branch replaces one slot by two ordered
slots. The first point with no pending slot ends the word. Structural
induction gives a unique parsed term and the code/parse round trips.
This is the existing constructor-word method, with explicit leaf labels.
The controller retains
one mutable address and one finite left/right continuation flag per
active ancestor. Appending or deleting an address letter and switching
a pending right continuation are paid finite list operations. A recursive
description of a visit supplies no runtime subtree, height, size or fuel:
the only constructor information used to schedule work is the reply just
acquired. The absent case is outside the promised runs; it is not silently
interpreted as a leaf.

**Theorem 54.2 (exact unknown entry and actual changed endpoint).** For
every finite entry $t\in\mathcal D$, every actual legal old producer word
ending there, and every installation satisfying Assumption 53.2, the same
controller of Definition 54.1 terminates. It returns an owned exact entry
code for $t$ and a distinct owned current code for the actual source
$\nu(t)$, on the same callable root and current authority. It visits
exactly $\mathcal L(t)$ in preorder, encounters no absent refusal, and
performs precisely one successful promotion at every entry $\alpha$
leaf and no other successful event.

Proof. A promotion adds a material marker but changes no logical branch,
logical position or logical descendant relation. Before any scheduled
visit, all earlier changes therefore lie at already visited entry leaves.
These leaves are incomparable with a later scheduled subtree. Every
scheduled target is the root or a child of a branch whose branch refusal
has already been obtained. It is an actual entry position, and no earlier
promotion changes its entry constructor. These assertions are an invariant
of the backed traversal, not information supplied to the controller.

Prove the visit assertion by induction on the finite entry subtree at its
scheduled address, allowing an arbitrary pending continuation outside that
subtree. At an entry $\alpha$, its actual $P$ succeeds, records the entry
$\alpha$ and leaves the actual $\beta$; no logical child is scheduled.
At an entry $\beta$, the actual wrong-type refusal leaves it unchanged
and records $\beta$. At a branch, the actual branch refusal leaves it
unchanged. The left and then right induction hypotheses apply because
their cones are disjoint. Their actual endpoints are $\nu(v),\nu(w)$,
and the assembled preorder words describe $\langle v,w\rangle$ and
$\langle\nu(v),\nu(w)\rangle$. The pending continuation receives no
unobserved subtree value.

Every visit uses one finite complete request and a finite returned reply;
the source template and finite backing supply each successful completion.
The induction proves finitely many visits and finite local stack work,
without a supplied stopping bound. It also proves that an absent answer
never occurs. The current code is assembled from the actual effects on
the very root being called, while the entry code records the constructors
before their first probes. At termination both result records have actual
owned backing, and the root reference and rights remain retained for
the continuation. Reading or exporting those codes is subsequent paid
use of these records. The endpoint is $\nu(t)$, not a restoration of
$t$. $\square$

## 55. The earned code predicts and serves the complete original P/S task

**Definition 55.1 (retained current predictor).** At an attached Ready
cut retain the canonical current constructor word $\widehat u$, the
actual callable dispatcher entry and its current rights, the finite
framing program, and owned scratch and pending-call backing. Store the
entry word in a separate immutable archive. In equations comparing a
code with a source term, identify the valid canonical code with its
uniquely parsed term. The predictive algorithm
navigates only $\widehat u$, with the logical blocking rule of
Definition 53.1, and evaluates the entire table of Definition 53.3.
On a predicted success it constructs the indicated finite code successor;
on a refusal or BadFrame it retains the current code. Hypothetical
prediction makes no source call. Finite word navigation and replacement
use ordinary acquired-code scans and backed stacks, not a future reply
oracle.

For real continued use, first compute the reply and code successor from
the current code and request. Then send that request through the retained
actual entry, consume its whole actual reply and return, and commit the
corresponding code update before another synchronized cut is exposed.
The pending request, predicted answer, code edit and continuation are
backed during the call. An incomplete input retains its actual prefix
and waits; it neither commits a code edit nor invents a reply. The
immutable entry archive is unchanged by this procedure.

**Theorem 55.2 (self-sufficient prediction with real callable use).**
The records returned by Theorem 54.2 initialize Definition 55.1 with
$\widehat u=u=\nu(t)$. For every finite common adaptive continuation
in $Q_A$, predictions terminate on complete frames and have exactly the
actual full replies and corresponding settled source successors at each
step. If those requests are actually forwarded, they execute on the
same bound source and reestablish $\widehat u=u$ after every return.
This includes successful $P$ and $S$, every refusal reason, unsupported
tags and arbitrarily long finite addresses. A finite completion of a
pending proper frame prefix resumes the same assertion.

Proof. The initial equality is acquired by Theorem 54.2. Suppose it
holds at a synchronized cut. Induction along the finite address proves
that code navigation and actual logical navigation either reach
corresponding constructors or first block at the same leaf. No code
step follows a beta marker. The four target cases in Definition 53.3
therefore agree, including the exact refusal reason. At a success the
original material template has exactly the displayed logical replacement,
and its Growth reply has the same kind and original requested address
as the prediction. Applying this replacement to the code restores its
equality with the actual logical term, including all newly created
positions. The source's reused and fresh vertices are those of Definition
53.1, not fresh objects chosen by the predictive calculation. Refusals
and unsupported tags preserve both source and code.

All code scans, finite replacements and framed output constructions
terminate on the acquired finite words. Source serialization, current
rights and sufficient material supply the corresponding real completed
call. There is no source-dependent selector hidden in the predictor.
After a complete reply, the pending update and finite cleanup establish
the next synchronized cut. Induction on completed requests now proves
the claim. A common policy can use its previous complete replies and
shared retained inputs to choose the next request; equal replies make
these choices agree. The same argument applies after fixing any common
random tape used by that subsequent policy. It does not give a randomized
acquisition lower bound.

For partial frames, induction on received bits gives the same parser
subphase and occupied backing for the actual prefix. Until completion
there is no source call or completed reply; a finite supplied suffix
returns to the complete-frame argument. Missing rights, interruption and
observable exhaustion are outside Assumption 53.2, not extra refusal
cases certified by this invariant. Thus a retained code is a finite
self-sufficient predictive description, and the separately retained
binding makes the proved continuation actual use. Neither property
creates the other one's access premises. $\square$

## 56. Current four-expression recovery and the separate entry archive

**Definition 56.1 (current views on the acquired process).** Consider
the synchronized cuts after Theorem 54.2 and after finite continued use
of Theorem 55.2. Fix the same dispatcher, root, current authority and
service contract as common context. For the actual current term $u$ set:

| View | Independently selected information |
| --- | --- |
| Space $S_A$ | Actual rooted oriented material-address support of $C(u)$, excluding observer record edges |
| Boundary $B_A$ | Actual terminal-material-address antichain of that same $C(u)$, exactly AA Definition 17.3's $B_0$ |
| Time $T_A$ | Labelled causal creation/lifecycle order $E(u)$ of AA Definition 17.1 for the actual successful source events |
| Memory $M_A$ | Contents of the actually retained current constructor code, with the same retained callable entry and current authority |

Boundary contains the terminal marker address $pL$ at a logical beta
leaf $p$; it contains $p$ at a logical alpha leaf. It is not the antichain
of logical growth targets. Time records the causal dependencies and
labelled membership of successful source events, including old producer
events and later actual successes; it chooses no total serial extension
and includes no refusal, printing or work events. Memory selects the
current predictor record, not every record in the joint process. The
immutable entry archive exists in that process and is additional data.

View equality and reconstruction concern their semantic contents in
this fixed common context. Re-encoding a recovered term gives the
description of the corresponding memory content; it is not a grant of
authority or recovery of private backing identities. The actual retained
memory and binding are supplied by Theorems 54.2–55.2. No additional raw
Space, Time or Boundary exposure port is assumed.

**Theorem 56.2 (the original P/S kernel needs no Tag port).** On the
domain of Definition 56.1, each current view has exactly the $Q_A$
task kernel: two current terms are task-equivalent if and only if they
are equal. The existing AA material-support and causal inverses give
mutual recovery of these views on their actual images; every route
returns the same current view. They commute with every completed $Q_A$
operation, its entire reply and its settled semantic successor. These
are current-source assertions, not inverses of the entry acquisition.

Proof. AA Definition 17.3 gives prefix closure from $B_A$ to $S_A$ and
maximal material addresses in the reverse direction, expressly including
unary markers. Arity parsing recovers the same $u$. AA Theorem 17.2
recovers that $u$ from $T_A$ and conversely specifies its causal event
order. Parsing $M_A$ gives $u$ by Theorem 55.2. These are the cited
existing inverses; they are not new general geometry or causal-recovery
theorems.

Equal terms give equal complete replies and logical successors by
Definition 53.3. Conversely, take unequal finite ordered terms and
descend through common binary branch constructors until reaching the
first different constructor. Its address $p$ is present in both terms:
if either current subtree were not a branch, that would already be the
first difference. At $p$, a single original $P_p$ separates all three
possibilities, since alpha gives Growth, beta gives wrong-type refusal,
and branch gives branch refusal. Thus no unavailable Tag call is needed
for this task separation. Equality of $u$ is its exact kernel.

All the described maps decode and re-encode the same $u$. Hence inverse
and triangle identities hold on actual images with the common binding
context preserved. For a success $e$, take the actual source replacement
and the new causal event at its actual address; this is the same
$E(u')$ whether calculated before or after conversion. For a refusal
or BadFrame nothing in these contents changes. Theorem 55.2 supplies
the full reply, actual callable step and synchronized code update.
Finite-request induction proves commutation, including source successors,
rather than only equality of static readouts. No assertion identifies
private allocation names, code-work duration or the intermediate pending
states with these current views. $\square$

**Proposition 56.3 (the entry archive is not current-view memory).**
Let $K$ be any nonempty finite ordered full binary logical skeleton. Give every
$L$-ending leaf type beta, and allow either type at each other leaf;
for a singleton skeleton its root is allowed either type. If there
are $m$ allowed-variable leaves, all $2^m$ entries belong to
$\mathcal D$ and have exactly the same normalized endpoint $\nu(t)$.
Their entry archives are different. Consequently none of the current
views at the acquisition endpoint recovers that archive on this family.

Proof. AA Theorem 17.2 admits every assignment with the stated leaf
constraint, and (AAII.13) makes all its leaves beta while retaining $K$.
Theorem 54.2 stores the different original assignments. The current
support, material boundary and causal order are functions of the common
normalized term; the current predictor code and its common retained
entry have that same content too. Already $\alpha$ and $\beta$ have
the common normalized endpoint beta, with different acquired entry
reports and different probe replies. Thus recovery of the archive
would not be single-valued. Exposing it or allowing a selector to read
it enlarges $Q_A$ and requires an appropriately supplemented view.
The result does not erase the archive from the actual joint process.
$\square$

## 57. Sharp deterministic fresh-source-vertex disturbance

**Definition 57.1 (reachable type family and competitors).** For the
skeleton $K$ in Proposition 56.3, let $F_K$ be its logical leaves and

$$
V_K=\begin{cases}
\{\varepsilon\},&K\text{ has no branch},\\
\{p\in F_K:p\text{ ends in }R\},&\text{otherwise},
\end{cases}
\qquad m=|V_K|.
\tag{AAII.14}
$$

For $x\in\{0,1\}^{V_K}$, let $t_x$ have alpha at $p$ when $x_p=0$,
beta when $x_p=1$, and beta at all leaves outside $V_K$. Internal
constructors are those of $K$. The finite family
$\mathcal F_K=\{t_x:x\in\{0,1\}^{V_K}\}$ is reachable from the
known-alpha origin. The current guard-only entry and all accessible
nonreply initial data are common over this family. Even the entire
logical skeleton $K$ may be supplied to a competitor; its leaf types
are not supplied.

A competitor is any deterministic effective guard-only controller,
with arbitrarily large paid finite records, which on every entry in
$\mathcal F_K$ returns the exact entry term after finitely many local
steps and completed calls, at a settled cut with no pending frame or edit.
It may use arbitrary finite addressed $P/S$
calls, refusals and unsupported frames, and may stop at a different
changed endpoint. Its disturbance $\Delta_A(t_x)$ is the number of
fresh source vertices actually allocated by its successful requests
before that return. Private work and code allocation are charged
separately and do not count as source vertices. No request permits a
source deletion or rollback.

**Lemma 57.2 (a variable leaf has no indirect guard read).** Fix
$p\in V_K$ and two entries differing only at $p$. Under the same
deterministic controller, their complete reply and local-control traces
coincide up to the first request directly targeting $p$. Before that
request, every completed request also leaves their current logical
terms differing only at the still unedited leaf $p$. Thus an exact
competitor must target every $p\in V_K$ on every terminating run.

Proof. A strict ancestor of $p$ is an original branch and always refuses
either growth kind there. No operation elsewhere can replace that branch.
A strict logical descendant of $p$ is absent in both variants, since
alpha and beta are both logical leaves. In particular a request to $pL$
does not read the material marker present in just one variant. A target
in an incomparable cone has identical logical content in the two runs;
its reply and any source edit agree there. Unsupported frames have the
same fixed reply. These cases exhaust requests not directly at $p$,
and preserve the asserted relation between current terms. Hidden
allocation counts, work duration and private fields give no extra output
by Assumption 53.2. Determinism and induction therefore give the same
local choices and complete replies before the first direct target.

If a run returned without directly targeting $p$, the flipped entry
would have the same finite transcript, the same stopping computation
and the same returned entry code. The two correct entry codes differ
at $p$, a contradiction. $\square$

**Theorem 57.3 (exact minimax source-vertex price).** For every finite
$K$, the deterministic exact competitors of Definition 57.1 satisfy

$$
\inf_A\ \max_{t\in\mathcal F_K}\Delta_A(t)=m.
\tag{AAII.15}
$$

The lower bound holds even with $K$ supplied and without requiring the
competitor's final source to equal $\nu(t)$. The controller of Definition
54.1, which needs no supplied $K$, attains the bound, returns that exact
endpoint, and admits the retained continuation of Theorem 55.2.

Proof. For the lower bound reveal entry bits only when a competitor
first targets their corresponding variable leaves. If that first
request is $P_p$, choose entry alpha there; if it is $S_p$, choose
entry beta. Before this request the chosen bit has influenced no reply,
by Lemma 57.2. In either case the still unedited target is exactly that
chosen type, so this first direct request succeeds. It adds respectively
one or two fresh source vertices.

This delayed choice defines one fixed admitted entry, rather than a
retroactively changing source. To see both consistency and finite progress,
consider any finite prefix at which some bits remain unchosen. All
completions of them are admitted entries giving the same preceding
trace. Choose one completion temporarily. Its controller must terminate
in finitely many steps. It cannot return before targeting every remaining
variable leaf, by Lemma 57.2. Hence the common computation reaches a next
first target at an unchosen leaf in finite time. Choose that bit as above;
this choice does not change any earlier reply or edit. Repeat at most
$m$ times. With all bits chosen, the resulting $t_x$ realizes the whole
constructed prefix; its remaining run terminates by the competitor's
totality. The $m$ distinct first-target successes have added at least
$m$ vertices. Further actions cannot delete them. Thus
$\max_x\Delta_A(t_x)\ge m$ for every competitor.

For the upper bound, only leaves in $V_K$ can be alpha. Theorem 54.2
adds exactly one vertex at each such alpha leaf and none elsewhere,
so its disturbance is at most $m$. The assignment making all $m$
variable leaves alpha attains $m$. This supplies an admitted competitor
and proves (AAII.15), without charging a supplied skeleton as acquired
knowledge. The all-alpha choice here concerns only the variable leaves;
every left-born leaf remains beta, including in the worst case.
$\square$

**Definition 57.4 (scope of sharpness).** Equation (AAII.15) optimizes
only fresh source vertices for deterministic exact entry recovery with
the declared guards and no extra readout. It is not a minimum number
of calls, a total-work or bit-price optimum, a randomized expected-cost
bound, or a physical disturbance principle. A supplied nondestructive
Tag or Native Read would distinguish leaf types without these promotions;
that stronger information interface is outside the competitor class.
The bound also does not characterize the cheaper task of predicting
only a chosen proper quotient of entry behavior or learning only a
changed current endpoint without reporting the entry.

## 58. The same run's traffic, material and retained use

**Definition 58.1 (parameters and literal backing).** On the actual
entry $t$, put

$$
a=\#\{\alpha\text{ leaves of }t\},\quad
b=\#\{\beta\text{ leaves of }t\},\quad L=a+b,\quad n=2L-1,
\qquad
D=\sum_{p\in\mathcal L(t)}|p|,\quad
D_\alpha=\sum_{\substack{p\in F(t)\\t|_p=\alpha}}|p|.
\tag{AAII.16}
$$

The two acquired words use distinct owned backing with a two-bit
constructor payload per logical node. Their list links, headers,
references, result slots and authority representations are additional.
One current address and ancestor continuation flags suffice for preorder
scheduling; source-side request and answer words have their own actual
backing until consumed. No archived copy of every request or hypothetical
successor is required. If such copies or external report copies are
retained, their actual material is additional.

**Proposition 58.2 (attained acquisition counts).** Definition 54.1's
actual acquisition uses precisely

$$
\begin{aligned}
\#P\text{ attempts}&=n,&\#S\text{ attempts}&=0,\\
\#\text{successful promotions}&=a,&
\#\text{fresh source vertices}&=a,\\
|C(t)|&=2a+3b-1,&|C(\nu(t))|&=3L-1,\\
I_{\rm acq}&=2D+4n,&O_{\rm acq}&=2D_\alpha+5n.
\end{aligned}
\tag{AAII.17}
$$

$I_{\rm acq},O_{\rm acq}$ count literal request and reply bits,
excluding the $n$ separate End, acknowledgement and Return operations.
Under the source-field convention of AA Proposition 22.1, these
promotions make $4a$ located parent/left/right assignments. With
root-based navigation and parent-chain return, the requests use $D$
logical child-link descents and $D$ parent-link ascents. The two
result words have $4n$ constructor payload bits in total.

Proof. Theorem 54.2 gives one $P$ attempt at every logical node, with
success exactly at the $a$ entry alpha leaves. A finite full binary
logical tree with $L$ leaves has $n=2L-1$ nodes. Its material tree adds
one marker for each of its $b$ beta leaves, giving $n+b$ vertices.
The $a$ promotions add one each and leave $L$ beta leaves, proving the
two material orders.

An address-$p$ request has $3+|A(p)|=2|p|+4$ bits. Every refusal reply
has five bits; a successful reply at an entry alpha contributes its
additional $2|p|$ bits. Summing over the actual visited nodes proves
the traffic identities. Every such target is present, so root descent
and the specified parent return each traverse its depth. A promotion
initializes the new marker's three source fields and writes its old
target's left attachment: four assignments, exactly as in AA Proposition
22.1. It appends no routing-tape cells in this minimal installation.
Finally both logical codes retain all $n$ nodes, each with a two-bit
constructor payload. $\square$

**Proposition 58.3 (preparation and finite continued-use account).** On
the same actual process the old preparation of $t$ used exactly $b$
successful promotions and $L-1$ successful splits. Its literal source
initialization and successful edits therefore used
$3+4b+8(L-1)$ located source-field assignments, before the $4a$
acquisition assignments. Its actual old addresses, communication,
allocation, grants and any records really retained remain paid resources,
even when their serial order is unavailable to the attaching observer.

For any subsequent completed continuation let $r$ be its number of
well-formed $P/S$ frames, $z$ its number of unsupported frames, $p_+$
and $s_+$ its successful promotion and split counts, and let $J$ be the
sum of requested address depths over those $r$ frames and $J_+$ the
sum over their successes. Its additional literal traffic is

$$
I_{\rm cont}=2J+4r+3z,\qquad
O_{\rm cont}=5r+2J_++3z,
\qquad
\Delta_{\rm cont}=p_++2s_+.
\tag{AAII.18}
$$

At that cut the source has $3L-1+p_++2s_+$ vertices, the current
logical word has $n+2s_+$ constructors, and the unchanged entry word
still has $n$. Their total constructor payload is $4n+4s_+$ bits.
The successful continuation templates use $4p_++8s_+$ further located
source-field assignments. Add every actual End, acknowledgement,
Return, partial-input bit already retained, code computation and
record edit at its actual width.

Proof. AA (AA.78) gives the old successful counts from the actual leaf
counts; this uses no reconstructed serial order. The old source-field
formula is AA Proposition 22.1 restricted to its source fields. Each
later source success has exactly its original one- or two-vertex
template. Only a split adds two logical nodes. The request and reply
lengths in Definition 53.3 yield (AAII.18) by direct summation,
including absent addresses and wrong-type or branch refusals among the
$r$ frames. Unsupported frames each contribute three input and three
output bits without growth. The archive is immutable and the current
word grows by four payload bits per split; the field counts again use
the same literal templates. $\square$

**Definition 58.4 (coexisting resources and parsimonious scope).** If
the entry height is $h$, the acquisition can use $O(h+1)$ address and
continuation symbols in addition to the two result words: retain a
single path, push a pending-right flag on entering a branch, switch
that path's last letter when entering its right child, and pop finished
ancestors. This does not retain a separate copied address for every
pending subtree. Each actual source address/reply buffer has its full
width, up to $2h+5$ bits during acquisition. Counters, parser state,
pending latches, allocator and program backing, actual source links,
references and grants coexist with these payloads. The local controller
does not receive the bound $h$ in advance.

After attachment, a finite current-code scan suffices to navigate each
request, and a finite word replacement suffices to prepare its exact
successor. A straightforward implementation may temporarily retain both
old and proposed words and the complete predicted and actual reply;
their simultaneous backing and cleanup are charged. The actual source
also exists throughout: none of the code counts replaces its material.
Exporting either result word adds its literal transmitted payload and
framing beyond (AAII.17). A finite instruction description implies
neither a fixed lifetime store nor a source-size-independent work bound.

For the current task the code and callable binding suffice; the immutable
entry archive is needed for the separate entry-report requirement and
may be dropped if that requirement is dropped. The exact task kernel of
Theorem 56.2 justifies retention of current syntax, but supplies no
whole-resource optimum for a particular code layout. The only claimed
optimal coordinate is (AAII.15).

## 59. Exact suppliers and the unresolved recovery domain

**Definition 59.1 (source and mathematical correspondence).** The
guard-only acquisition of the unknown entry with its actual normalized
endpoint, joined to complete retained original $P/S$ use and the sharp
reachable-family source-vertex price, is `repo-derived` on Assumption
53.2. The following are suppliers, rather than new general traversal,
causal-inverse, predictive-quotient or history-retention results.

| Supplier | Exact content reused and distinction retained |
| --- | --- |
| [AA §§17,20–23](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction) | Birth typing, reachability, material unary markers, causal reconstruction, the original guards, source templates, frames and located source-field counts are reused. Its owned known-alpha seven-request installation constructs full order records from its own choices; it does not provide this late-entry guard-only observation. Current material and causal inverses are credited in Theorem 56.2. |
| [AAII §§47–52](#47-source-bound-compressed-records-for-the-complete-lab-history) | Existing source-paid compressed full-order records and exact seven-request continued use remain valid under their known-alpha initialization. A code of the unknown entry obtained here is not a reconstruction of those missing old ranks or routing words. |
| [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean), [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | `Frame`, `Control`, `sourceControl`, `initialControl`, `native_source_producer` and private `traverse`, `production_reads`, `stationary` already supply a source-independent backed preorder producer with one actual Native read per node and exact finite termination. Here that literal four-valued nondestructive read port is absent. A successful $P$ supplies constructor information while changing the same source, so the two-code and changed-endpoint invariant is essential. |
| [NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean), [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs), and [PreorderTreeEvaluation](../../../D5/S0/Computability/PreorderTreeEvaluation.lean) | `term_at_prim`, `readout_prim`, private `treeView`, `child`, `walkStep`, `walk_exact`, `rootReply`, `readout_walk`, and the constructor-word evaluator supply given-code navigation and finite stack methods. Their native logical syntax matches the code navigation, not the material beta marker or the LAB source edit. No new primitive-recursion certification is asserted here. |
| [LAB Spent-Trigger Acquisition, Definition 3.1 and §§4–5](RECURSIVE_RELATIONAL_OBSERVATION_LAB_SPENT_TRIGGER_ACQUISITION.md#3-sharp-incremental-acquisition-after-paid-stationary-observation) | Its stationary prepass really uses Tag and FetchSelected, followed by acquisition of a selector distinction and retained selected service. Those stronger ports and its old selected records are not supplied by Assumption 53.2. Its incremental source-growth optimum addresses a different unknown and does not replace the type-family bound (AAII.15). |
| [AA §§41–46](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#41-隐藏安装的取得目标与跨候选接口) | Self-sufficient prediction and current-source candidate elimination already exist for finitely presented unknown selector installations from the known alpha seed. Their old source is tracked from known initialization and actual Growth replies; it is not the unknown entry syntax in this guard-only problem. |
| [Native Leaf Boundary Acquisition, §§10–16](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md#10-a-changed-installation-ordered-leaf-waves-on-the-actual-lab-material) | Original LAB guard/source correspondence, full field-and-growth prediction and its current four-view domain already exist under authentic ordered terminal ports, calibrated Reset/Add/Read/Tick/Hold and a unit-adjacency law. None of that field/roster apparatus is used here. Nondestructive acquisition there remains sufficient when its stronger installation is supplied. |
| [PG §40](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), [PVC](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), [NCR §8](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), [Structural Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md), and [Transport Memory Completion §57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) | Task-relative visibility, retained same-source access, paid conversion/use and distinctions between causal and total chronology are existing methods under their own source, initialization and tariff contracts. The present result supplies neither their fixed original ports nor a replacement proof of their unresolved original obligations. |
| Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, [Algebra/Free](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Free.lean) and [Computability/Primrec/List](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Primrec/List.lean) | `FreeMagma.of`, `FreeMagma.mul`, `FreeMagma.lift`, `Primrec.list_foldl` and `Primrec.list_foldr` supply finite constructor folds and backed-list computation. These are computation suppliers; they do not give a source observation, current right or a guard-disturbance bound. |
| [Bennett, *Logical Reversibility of Computation*, introduction](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html) | `literature-attested`: retaining input/output information and computation history is an established way to preserve distinctions erased by a many-to-one computation. The separate entry archive uses that elementary distinction. No reversible LAB dynamics, source restoration or thermodynamic conclusion is imported. |

The proof of (AAII.15) uses ordinary transcript indistinguishability and
a consistent adversary. The source-specific content is that all $2^m$
birth-legal assignments are reachable, strict logical descendants cannot
read a beta marker, and either possible first direct guard can be made
to perform a persistent source edit. Removing these source facts leaves
no claimed new general decision-tree lower-bound principle. Likewise
the current-view maps are credited existing inverses; the additional
operational bridge is their attained guard-only entrance and retained
continuation on the actual changed endpoint. This attribution makes no
exhaustive worldwide originality claim.

**Definition 59.2 (remaining mathematical boundaries).** The proved
entrance requires an authentic original-root LAB dispatcher, the
birth-reachable source promise, exactly the stated refusal distinctions,
present authority, serialized completion and sufficient finite material.
These premises are not learned from the acquired code. Identical
observable frames from an inauthentic service would not certify their
physical truth. Additional metadata, revocation, crashes, quotas or
nonexclusive changes require a new observation/successor contract.

The result acquires the old entry syntax and the real current syntax,
not the old successful-event serialization, old routing records or
complete controller chronology. It does not return the source to its
entry term, install arithmetic or field services, recover raw physical
identities, invert arbitrary busy cuts, or infer authority from a
description. An arithmetic projection of either code is only a computed
projection unless its own callable arithmetic installation is supplied.
The current-view theorem excludes the entry archive from its task and
states that exclusion explicitly; it supplies no inverse for that
larger archived state.

All original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization, terminal and final-no-Ready questions keep
their exact scopes. This guard-only late attachment does not settle
them or change the old seven-request history claims. A physical
realization, a universal reduction to alpha/beta generation, a single
globally optimal relation structure, an actually realized infinite
run and the unrestricted common-process space/time/boundary/memory
programme remain separate obligations. The statements here are ordinary
mathematical proofs, without new Lean certification.

## 追加锚（本行以下为增补区）

## 60. A sharp history floor for the existing local-rank payload

**Definition 60.1 (conditional history content at the original Ready cut).**
Use exactly AA §§17,19–23's LAB, its actually allocated known-alpha
root, and Definitions 47.2 and 50.1's full seven-request $Q_g$ service
and local-rank layout. The domain consists of its finite returned Ready
cuts, with the same source binding, current rights and backing. It is
not the guard-only unknown-entry task of §§53–59. For the actual reachable
term $t$, let $\mathcal H(t)$ be its complete successful $P/S$ histories
from that alpha. In this section write

$$
\begin{aligned}
F(t)&=|\mathcal H(t)|=F_{PS}(t)=\prod_{v\in I(t)}R_v,
& R_v&=\binom{x_v+y_v}{x_v},\\
x_v&=e_\beta(t_{vL}),&y_v&=e_\alpha(t_{vR}),\\
h(t)&=|\{v\in I(t):x_v>0,\ y_v>0\}|=H(t),\\
B(t)&=\sum_{v\in I(t)}\lceil\log_2R_v\rceil,
&G(t)&=\lceil\log_2F(t)\rceil.
\end{aligned}
\tag{AAII.16}
$$

Thus $F$ here counts histories, not the leaf antichain denoted by $F$
in §53; $h$ is exactly the number of live local headers. The born-type
event count is AA (AA.73): a subtree $u$ born $b$, with $a$ alpha and
$c$ beta leaves, has $e_b(u)=a+2c-1-\mathbf1_{\{b=\beta\}}$.
All logarithms here have base two; an empty product is one and $0!=1$.

$G$ is conditional fixed-width history content: fix the bare source
$t$, known initialization, binding/rights and returned phase, and supply
no other history-dependent side information. A $g$-bit supplement for
all these histories has at most $2^g$ conditional values. Any additional
history-bearing allocation pattern, occupancy, pointer, header or control
state must be included in that supplement's information; it cannot be
silently treated as fixed context. The common bare source itself is
conditioned on, rather than charged as a history supplement. This is
neither a variable-length average-code claim nor a total-resource bit
count. $B$ is the bit payload of the already installed local layout;
$G$ does not name an installed global packing algorithm.

**Lemma 60.2 (event supply below ambiguous branches).** For every
birth-admissible subtree $u$, define $h(u)$ by the same local formula as
in (AAII.16). Then

$$
e_b(u)=0\ \Longrightarrow\ h(u)=0,\qquad
e_b(u)>0\ \Longrightarrow\ e_b(u)\ge2h(u)+1.
\tag{AAII.17}
$$

Proof. An admissible leaf has event count zero, except for beta born
alpha, whose count is one; all have $h=0$. An alpha leaf born beta is
inadmissible. At a branch write $x=e_\beta(u_L)$, $y=e_\alpha(u_R)$,
$a=h(u_L)$ and $b'=h(u_R)$. Its forced root prefix has length
$\kappa_\alpha=2$ or $\kappa_\beta=1$, so
$e_b(u)=\kappa_b+x+y>0$. If both child counts are positive, induction
gives $x\ge2a+1$, $y\ge2b'+1$, and
$h(u)=a+b'+1$. Hence $e_b(u)\ge2h(u)+1$. If precisely one count is
positive, the other child's $h$ is zero by induction, and the positive
child alone gives $x+y\ge2h(u)+1$. If both vanish, $h(u)=0$ and the
nonempty root prefix suffices. These cases also prove that a zero event
count has no ambiguous branch. $\square$

**Theorem 60.3 (attained factorial floor).** Every source in Definition
60.1 satisfies

$$
F(t)\ge2^{h(t)}h(t)!.
\tag{AAII.18}
$$

For every integer $h\ge0$, equality is attained by an actual reachable
source with exactly $h$ live headers, in the same known-alpha service.

Proof. Apply structural induction to the product of local radices on
birth-admissible subtrees. A leaf has product one and $h=0$. At a branch
retain $x,y,a,b'$ from Lemma 60.2. If $x=0$ or $y=0$, its radix is one
and the zero-event child has no ambiguity; the other child supplies
the required bound for the entire subtree. This includes $x=y=0$.
If both are positive, put $q=a+b'+1$. Lemma 60.2 and separate
monotonicity of $\binom{x+y}{x}$ in the nonnegative integers $x,y$ give

$$
R\ge\binom{2q}{2a+1}\ge2q\binom{q-1}{a}.
\tag{AAII.19}
$$

For the second inequality, partition a $2q$-element set into $q$ named
pairs. Among its $(2a+1)$-element subsets, count those with exactly one
split pair: choose that pair, one of its two members, and $a$ complete
pairs among the remaining $q-1$. This gives
$2q\binom{q-1}{a}$ distinct subsets. The first inequality also follows
directly by increasing $x$ or $y$ one at a time in the factorial formula
for a binomial coefficient. Multiplying (AAII.19) by the two inductive
bounds gives

$$
R\,(2^a a!)\,(2^{b'}b'!)
\ge2q\frac{(q-1)!}{a!b'!}\,2^{q-1}a!b'!
=2^q q!.
$$

Since $q$ is this subtree's $h$, induction proves (AAII.18), using AA
Theorem 19.2's history-product identity at the actual alpha root.

For attainment define

$$
t_0=\langle\beta,\alpha\rangle,\qquad
t_{h+1}=\langle t_h,\beta\rangle.
\tag{AAII.20}
$$

As a beta-born subtree, $t_h$ has event count $2h+1$: the base needs
one split, and the next branch has prefix one, left count $2h+1$ and
right count one. The base branch has radix one. In the recursive term decomposition,
the outer factor has radix $2h+2$, and the internal factors of its left
term are exactly those of $t_h$. Thus $h(t_h)=h$ and
$F(t_h)=\prod_{j=1}^h(2j)=2^h h!$. Being born alpha at the whole root
adds its forced promotion and changes neither these child counts nor
the history product.

These terms occur along one nested sequence of actual legal growth
words. Execute $P_\varepsilon;S_\varepsilon$ to obtain $t_0$. In $t_h$
the deepest beta leaf is at $L^{h+1}$ and the sole alpha is at
$L^hR$. Execute $S_{L^{h+1}}$ and then $P_{L^hR}$. The latter promotes
the **old bottom branch's** right alpha, which is still at that address;
it does not promote the newly created right alpha at $L^{h+1}R$.
The old bottom subtree $\langle\beta,\alpha\rangle$ becomes
$\langle\langle\beta,\alpha\rangle,\beta\rangle$, giving exactly
$t_{h+1}$. Both guards are enabled. The original driver and Theorem
49.1 supply the actual framed calls, maintenance, outputs, acknowledgement
and Return after each event. At $t_h$ the same run has
$P=S=h+1$ and $V=1+P+2S=3h+4$ source vertices. Its nontrivial radices
are $2,4,\ldots,2h$, so its actual payload and conditional width are
$B(t_h)=\sum_{j=1}^h\lceil\log_2(2j)\rceil$ and
$G(t_h)=\lceil h+\log_2(h!)\rceil$. Each finite prefix has its supplied
finite backing; no completed infinite physical run is used. $\square$

**Corollary 60.4 (integer rounding and uniform relative overhead).**
For every source in Definition 60.1,

$$
\begin{cases}
F=1,\quad B=G=0,&h=0,\\
0\le B-G\le h-1,\quad
G\ge\lceil h+\log_2(h!)\rceil,&h\ge1.
\end{cases}
\tag{AAII.21}
$$

For integer $g\ge0$ set
$K(g)=\max\{j\ge0:2^j j!\le2^g\}$. It is finite and $K(0)=0$.
Whenever $G\ge1$,

$$
G\le B\le G+K(G)-1,\qquad
K(g)=O\!\left(\frac{g}{\log_2(g+2)}\right)\quad(g\longrightarrow\infty).
\tag{AAII.22}
$$

Consequently $B/G\to1$ uniformly over reachable sources as $G\to\infty$.
This is uniform sublinear relative rounding overhead for the existing
local bit payload, with no change to its operational installation.

Proof. A local radix is one exactly when one child count is zero.
Thus $h=0$ gives $F=1$ and $B=G=0$, and $h>0$ gives $F>1$.
The elementary ceiling inequalities give
$G=\lceil\sum_v\log_2R_v\rceil\le B$ and, for $h>0$,
$B<\log_2F+h\le G+h$. Integrality yields $B-G\le h-1$.
The factorial lower bound gives the remaining inequality in (AAII.21)
and $h\le K(G)$, since $2^h h!\le F\le2^G$.

For $j\ge2$, at least $j/2$ factors of $j!$ are at least $j/2$, so
$\log_2(2^j j!)\ge(j/2)(1+\log_2j)$. If $2^j j!\le2^g$ and
$j>\sqrt g$, this implies $j\le4g/\log_2g$ for $g>1$; otherwise
$j\le\sqrt g$. These two bounds, with $j=0,1$ included, prove the
stated asymptotic bound on $K$. Dividing (AAII.22) by $G$ gives a bound
independent of $t$ that tends to one. The case $G=0$ is already exact,
and no ratio with zero denominator is asserted. $\square$

**Definition 60.5 (credited content and the resource distinction).**
AA Theorem 19.2 supplies the product and the source-to-history inverse;
Theorems 47.3 and 49.1–49.2 supply acquired rank values and the complete
original FetchGrowth/Next service and successors; Theorem 51.2 supplies
the annotated four-view correspondence. Those constructions and proofs
are reused. Distinct histories in one fixed-source fibre differ at an
indexed event, so the original FetchGrowth already separates them.
Thus the fixed-width complement needs $2^g\ge F$ and at least $G$ bits.
This is the supplied conditional alphabet principle, not a newly
installed consumer or acquisition of an unknown old history.

Enumerative ranking and its inverse are classical; the exact arithmetic
supplier remains [Cover, *Enumerative Source Encoding*, §I Propositions
1–2 and §II Example 2](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf),
as used in §52. The general counting of increasing rooted-tree orders
is also classical; see [Kuba, *A Note on Hook Length Formulas for Trees*,
§3.2](https://arxiv.org/pdf/1004.1883v1). That hook-length count is
background, not an asserted supplier of (AAII.18)'s extremum in terms
of the number of ambiguous LAB coordinates. The `repo-derived` delta
here is the sharp born-type factorial floor with its actual equality
family and the resulting uniform refinement of the existing rounding
estimate (AAII.8). The proof uses elementary pair-subset counting and
ceilings; no worldwide novelty or new Lean verification is claimed.

The comparison $B$ versus $G$ concerns only conditional history payload.
All actual material of (AAII.7) remains: the source and its three edge
reference fields per vertex, its auxiliary slots, the $h$ headers with
two references each, and the $B$ rank-cell next references in addition
to the $B$ payload bits. Actual reference widths, descriptors, allocator
state, retained cleared capacity, arithmetic/traversal work, program,
request/output backing, bindings, current rights and callable consumers
are further resources. No part of them is bounded by $B-G$, and no
actual local rank value is acquired from the source by this estimate.
It installs no $G$-bit global packer, gives no total-resource optimum,
and asserts no optimal upper rounding loss among LAB families. Earlier
operational abstention remains valid for its original acquisition task:
counting or more tightly bounding a missing historical value does not
supply it. Guard-only late attachment and full historical recall remain
different services. Every original fixed-model obligation and the full
common-process four-expression programme retains its prior scope.

## 追加锚（本行以下为增补区）
## 61. Randomized exact acquisition on one fixed entry

**Definition 61.1 (source, randomness and quantified competitors).** Keep
Definitions 53.1–53.3 and 57.1 without enlarging the source interface.
In particular, the actual source has a known-alpha origin but an unknown
current entry $t\in\mathcal D$; its old legal producer word is not an
input to the attaching controller. The same opaque bound root, orientation,
exclusive current $P/S$ rights, serialization, complete replies and local
return acknowledgement are supplied. There is no Tag, Native Read,
field, membership, history, allocation-name, duration or quota readout.
The beta marker is material and is never a logical child. Source-dependent
work records are initially empty. The finite framing and controller
program, source backing, owned work, references, grants, preparation,
communication, retention and clearing have their actual costs under
Assumption 53.2.

Add one separately supplied callable service delivering independent fair
bits. Its law is independent of the entry, every compatible old producer
word, source names and dispatcher state. Its binding, invocation rights,
provider work and delivered traffic are paid resources. This is an
explicit randomness premise, not a service constructed from the growth
guards or obtained from a computed current representation. The service
supplies no source-dependent information. Its product probability space
is a semantic description of random choices; it does not assert that an
infinite physical tape has already been allocated.

A randomized competitor is an effective measurable controller using only
these services and ordinary paid local computation. For every fixed
admitted entry and every fixed compatible old producer word, it must
return, with zero error, an exact entry constructor word and an exact
constructor word for its actual current source. It retains the actual
callable root and current rights and returns at a synchronized settled
cut. It must finish after finitely many local steps, fair bits and
completed requests with probability one. No erroneous returned word is
allowed; a null set of nonterminating tapes is permitted. No uniform
bound over random tapes is required. Expectations below are over this
independent service after the entry and its old preparation have been
fixed. Nonnegative costs may have infinite expectation for a competitor.
Sufficient finite backing is required for each claimed finite execution;
observable exhaustion is outside this installation.

For a finite full ordered binary skeleton $K$, use precisely
$\mathcal F_K,V_K,m$ of Definition 57.1: all nonvariable leaves are beta,
and the $m\ge1$ root-or-right-born variable leaves vary independently
between alpha and beta. All $2^m$ assignments are reachable by AA
Theorem 17.2. A competitor may even be given $K$ when proving a lower
bound. The attaining controller below is one source-independent program
for every finite $t\in\mathcal D$, with no supplied skeleton, height,
size, fuel or leaf types. Old preparation choices cannot be used as an
extra correlated input. All results are uniform over compatible old
legal histories satisfying the same attachment contract.

**Definition 61.2 (the weighted source coordinate).** On an acquisition
run let $P_+,S_+$ count actual successful promotions and splits before
return. Set

$$
G=P_++S_+,\qquad \Delta=P_++2S_+.
\tag{AAII.23}
$$

Here $G$ counts successful growth events and $\Delta$ counts fresh
persistent source vertices. Refused requests, code allocation and random
bits have other charges. For public rational weights $u,v\ge0$ with
$u+v>0$, define

$$
c_P=u+v,\qquad c_S=u+2v,\qquad
q=\frac{c_S}{c_P+c_S},\qquad
\kappa=\frac{c_Pc_S}{c_P+c_S}.
\tag{AAII.24}
$$

Thus $uG+v\Delta=c_PP_++c_SS_+$,
$1/2\le q\le2/3$, and $qc_P=(1-q)c_S=\kappa$.
These are fees for successful source changes, not for attempts. The
weights, their arithmetic and the sampler description are paid public
program data. The optimized coordinate excludes their costs; §65 retains
them in the same run's resource account.

**Lemma 61.3 (paired runs with a common tape).** Fix a compatible
installation, $p\in V_K$, the types at all other leaves and one fair-bit
tape. Up to the first well-formed $P/S$ request directly targeting $p$,
the two runs with opposite entry types at $p$ have identical accessible
traces, local choices and consumed-bit prefixes. If both runs return
correct entry words, each must make such a request, and their first
such request has the same kind.

Proof. With the tape fixed the controller is deterministic. Lemma 57.2's
cases still exhaust every possible earlier source observation: a strict
ancestor is a permanent branch; a strict logical descendant is absent
in both variants; an incomparable cone has identical content and edits;
unsupported frames have fixed replies. In particular, targeting the
material beta marker's address reads no extra logical position. Local
computations and random-service calls also agree because their supplied
inputs and the consumed tape prefixes agree. Induction preserves the
paired relation and the common control trace. Incomplete frames disclose
no additional reply. If either run returned before a direct request,
the other would return the same word on the same finite trace. Both
words cannot be correct. The first direct request is therefore present
on every tape on which both runs return correctly, and its kind agrees.
$\square$

## 62. Two actual randomized acquisitions and their endpoint laws

**Definition 62.1 (a paid exact rational draw).** For $q=k/d\in(0,1)$
in reduced form, use the classical binary-digit/geometric-index
Bernoulli construction. Start with $r_0=k$. At each iteration compute

$$
e_j=\left\lfloor\frac{2r_{j-1}}d\right\rfloor,
\qquad r_j=2r_{j-1}-de_j,
\tag{AAII.25}
$$

then request one fair bit. If that bit is one, return the current digit
$e_j$; otherwise repeat with $r_j$. The displayed index labels the
mathematical iterations; the implementation needs no growing index
counter. Remainder zero continues to produce zero digits. If $q=1/2$,
use a single fair bit directly instead. This sampler is a classical
supplier, not a new Bernoulli result: Lumbroso, *Optimal Discrete Uniform
Generation from Coin Flips, and Applications*, Appendix B,
[version 1](https://arxiv.org/abs/1304.1916v1).

Indeed $0\le r_j<d$, and repeated division gives
$q=\sum_{i=1}^j e_i2^{-i}+r_j/(d2^j)$. The remainder term tends to zero.
If $J$ is the first one in the fair-bit sequence, then
$\Pr(J=j)=2^{-j}$, $\Pr(J=\infty)=0$, and
$\mathbb E J=\sum_{j\ge1}\Pr(J\ge j)=2$.
Consequently the returned digit is one with probability
$\sum_{j\ge1}e_j2^{-j}=q$. Doubling, comparison and subtraction use
finite arithmetic on $O(\log d)$ bits of remainder storage, with a
fixed paid denominator. They take finitely many steps per iteration.
The direct half-probability draw uses exactly one bit. These facts
establish exact sampling, almost-sure termination and the stated mean
bit bills, without any general bit-optimality claim.

**Definition 62.2 (reply-driven traversal of original nodes).** Call a
position eligible when it is the root or its address ends in $R$.
At an original $L$-ending scheduled position issue $P$. At each eligible
scheduled position issue $P$ in mode one and $S$ in mode zero. There
are two implementations:

- GLOBAL obtains one $q$-draw before traversal and uses that same mode
  at every eligible position.
- LOCAL obtains a fresh independent $q$-draw at every eligible visit,
  including visits which turn out to be branches.

Both begin at the root and otherwise use the backed preorder traversal
of Definition 54.1. The following table gives the complete interpretation
of an actual returned answer at a scheduled target. Codes use that
same supplied two-bit constructor syntax.

| Request and actual answer | Entry subtree recorded | Current subtree recorded | Further visits |
| --- | --- | --- | --- |
| Either kind, Refusal(branch) | Branch, then acquired children | Branch, then acquired current children | Left, then right |
| $P$, Growth$(P,p)$ | $\alpha$ | $\beta$ | None |
| $P$, Refusal(wrong type) | $\beta$ | $\beta$ | None |
| $S$, Refusal(wrong type) | $\alpha$ | $\alpha$ | None |
| $S$, Growth$(S,p)$ | $\beta$ | $\langle\beta,\alpha\rangle$ | None |

A successful split finishes this original-leaf visit. Its two newborn
logical children are written into the current word and are not scheduled
as acquisition targets. The remaining children to visit come exclusively
from branch refusals already acquired at original nodes. The absent
case is excluded by the invariant proved below, not decoded as a leaf.
Every complete answer, End, acknowledgement and Return is actually
consumed before proceeding. Draws occur in the observer and never
replace a guard reply.

**Theorem 62.3 (earned entry and actual random endpoint).** For every
finite entry in $\mathcal D$, every compatible fixed old producer word
and every installation of Definition 61.1, both implementations terminate
almost surely and return exact, separately owned entry and current
codes. They visit each original logical node exactly once and no other
node; they retain the same callable source and current authority. Their
actual endpoint is obtained by the following replacements at original
leaves, leaving original branches fixed:

$$
\begin{array}{c|cc}
 &\text{mode one}&\text{mode zero}\\ \hline
\alpha&\beta&\alpha\\
\beta\text{ at an eligible leaf}&\beta&\langle\beta,\alpha\rangle\\
\beta\text{ at an }L\text{-ending leaf}&\beta&\beta
\end{array}
\tag{AAII.26}
$$

For GLOBAL the endpoint is $\nu(t)$ with probability $q$ and $\psi(t)$
with probability $1-q$, where $\psi$ leaves original alpha and
$L$-ending beta leaves unchanged and splits every eligible original beta
leaf once. For LOCAL the eligible original leaves receive independent
modes, and (AAII.26) gives the actual mixed endpoint. The endpoint laws
have the same one-leaf marginals. They differ when $m\ge2$: LOCAL
assigns positive probability to mixed leaf modes, whereas GLOBAL does
not. When $m=1$ their endpoint laws coincide, although their sampling
bills can still differ because LOCAL also samples eligible branches.

Proof. Before a scheduled visit, earlier source changes occur only in
finished original leaf cones. Distinct original leaves are incomparable,
so such changes do not modify an unvisited original subtree or its
navigation path. Every newly scheduled nonroot is a child of an original
branch whose branch refusal has already been consumed. Original branches
are never replaced. These assertions hold at initialization and after
each case in the table. A beta marker is never scheduled.

Induct on the finite original subtree, allowing an arbitrary backed
pending continuation outside it. At an original alpha, its address is
eligible by the definition of $\mathcal D$. A $P$ success or $S$
wrong-type refusal therefore identifies exactly that entry alpha and
gives the current leaf in (AAII.26). At an original beta, either a $P$
wrong-type refusal or an eligible $S$ success identifies exactly that
entry beta. The latter records the entire actual newborn pair without
recursing into it. At an original branch both kinds refuse as branch;
the left and then right induction hypotheses apply in disjoint cones.
The assembled original word is the original branch with its original
children, and the assembled current word is the actual branch with
their actual changed children. No case targets an absent position.
The continuations receive no unobserved subtree as an input.

The finite original tree bounds the number of scheduled visits even
though the controller does not know that bound. Each visit has finite
framing, source work, code work and return under the attachment contract.
GLOBAL uses one almost-surely terminating draw. LOCAL uses finitely many
such draws. Successive blocks of independent fair bits after a finite
stopping prefix are fresh: for each fixed finite prefix realizing its
stop, the remaining cylinder probabilities are again the fair product
probabilities. Summing over these disjoint prefixes proves independence
of successive returned modes. Thus the exceptional nontermination set
has probability zero in both implementations. The table proves the two
endpoint descriptions, and final ownership and retention are exactly
those required by Definition 61.1. $\square$

## 63. Sharp rational weighted fixed-input minimax

**Theorem 63.1 (randomized weighted source price).** For every finite
skeleton $K$ and every pair of weights in Definition 61.2, the randomized
competitors of Definition 61.1 satisfy

$$
\inf_A\ \max_{t\in\mathcal F_K}
\mathbb E\bigl[uG_A(t)+v\Delta_A(t)\bigr]
=m\kappa
=\frac{m(u+v)(u+2v)}{2u+3v}.
\tag{AAII.27}
$$

The input and its compatible old producer word are fixed before the
randomness is drawn. The lower bound holds even with $K$ supplied, and
even if the competitor may stop at any legally changed endpoint. Both
GLOBAL and LOCAL attain it, together with exact entry/current output
and retained full $Q_A$ use as proved in §66. Neither needs $K$.

Proof. First fix any competitor. Over the finite family
$\mathcal F_K$, intersect its probability-one sets of correct terminating
tapes, using a fixed compatible old preparation for each entry. The
intersection still has probability one. On every tape in it, Lemma 61.3
forces a first direct request at each $p\in V_K$. All coupled traces
use the same tape; no independence between different adaptive requests
is being assumed.

For a proof-only distribution, independently assign alpha probability
$q$ and beta probability $1-q$ to each variable entry leaf, independently
of the tape. This is a distribution over fixed admitted inputs, not an
observable prior supplied to the competitor. Fix a good tape and all
entry types other than the one at $p$. The two paired runs have the
same first direct kind at $p$. That target is still its unedited original
leaf. If the kind is $P$, its first request succeeds precisely in the
alpha variant, and its expected first-success fee under this one bit is
$qc_P=\kappa$. If the kind is $S$, it succeeds precisely in the beta
variant, and that expected fee is $(1-q)c_S=\kappa$.

Different original variable leaves yield distinct first-target requests
and distinct source successes whenever those requests succeed. All other
success fees are nonnegative, and the source has no deletion or rollback.
Thus the total weighted fee is at least the sum of these first-target
fees on each run. Average first over the paired entry bits, then the
other entry bits and the tape. Finite sums of nonnegative variables give

$$
\sum_{t\in\mathcal F_K}\mu_q(t)
\mathbb E[uG_A(t)+v\Delta_A(t)]\ \ge\ m\kappa.
\tag{AAII.28}
$$

The same statement holds with infinite expectations. Since the left side
is a convex combination of fixed-input expectations, some fixed entry
has expectation at least $m\kappa$. The maximizing entry is not selected
after observing a realized tape. Compatible old histories affect none
of the paired observations under Assumption 53.2; the argument works
for every such choice of histories.

For the upper bound let $a$ be the number of original alpha leaves and
$b_V$ the number of eligible original beta leaves. On
$\mathcal F_K$, $a+b_V=m$. In either attaining construction an original
alpha is promoted with probability $q$, an eligible original beta is
split with probability $1-q$, and an $L$-ending original beta is unchanged.
Theorem 62.3 excludes every other success. Linearity of expectation,
which requires no independence between leaves, gives

$$
\mathbb E P_+=qa,\qquad \mathbb E S_+=(1-q)b_V,
\qquad
\mathbb E[uG+v\Delta]=qac_P+(1-q)b_Vc_S=m\kappa.
\tag{AAII.29}
$$

This holds for every fixed entry and every compatible old history. The
sampler and acquisition satisfy the zero-error, almost-sure finiteness
and paid-backing contract; §66 establishes the full retained service.
They are therefore admitted competitors. Together the bounds prove
(AAII.27). $\square$

**Corollary 63.2 (two coordinate optima and their incompatibility).**
Fresh source vertices alone have minimax expected price $2m/3$, attained
with $q=2/3$. Successful growth events alone have minimax expected price
$m/2$, attained with $q=1/2$. No one competitor attains both worst-input
bounds simultaneously.

Proof. Apply Theorem 63.1 with $(u,v)=(0,1)$ and $(1,0)$ respectively.
If a competitor had both $\max_t\mathbb EG(t)\le m/2$ and
$\max_t\mathbb E\Delta(t)\le2m/3$, then every fixed entry would satisfy
$\mathbb E(G+\Delta)\le7m/6$. The same theorem with $u=v=1$ requires
a fixed entry with expectation at least $6m/5$. Since $m\ge1$ and
$7/6<6/5$, this is impossible. This argument compares coordinates on
the same runs; it does not add separately attainable optima as though
they were jointly attainable. $\square$

## 64. Deterministic and fixed-normalized-endpoint boundaries

**Proposition 64.1 (deterministic weighted benchmark).** With the same
entry family and exact output/retained-use requirements, deterministic
competitors have weighted minimax price $mc_P$. The all-$P$ traversal
of Definition 54.1 attains this price at endpoint $\nu(t)$.

Proof. The delayed assignment proof of Theorem 57.3 applies unchanged:
choose original alpha when a variable leaf's first direct kind is $P$,
and original beta when it is $S$. It defines one fixed admitted entry
and forces one success per variable leaf. Its fee is at least $c_P$,
because $c_S\ge c_P$. The finite-completion argument in that proof
ensures the constructed entry really reaches every such first target;
no infinitely postponed assignment is used. Later fees cannot subtract
from these fees. Conversely the all-$P$ traversal promotes each original
alpha once and changes no other leaf. Its fee is $c_Pa\le c_Pm$, and
the all-alpha assignment on $V_K$ attains equality. $\square$

**Theorem 64.2 (prescribing the actual endpoint removes the gain).**
Restrict randomized competitors to those whose actual returned source
must equal the original normalized term $\nu(t)$ almost surely, with
exact entry output and retained callable use. Then

$$
\inf_A\ \max_{t\in\mathcal F_K}
\mathbb E[uG_A(t)+v\Delta_A(t)]=mc_P.
\tag{AAII.30}
$$

More precisely, every terminating run with that endpoint has exactly
$a$ successful promotions and no successful split, where $a$ is its
entry alpha count. Its fee is pathwise $c_Pa$.

Proof. A successful split creates a binary branch at a former leaf.
No allowed later operation removes a branch, its logical children or
its material vertices. The branch set of $\nu(t)$ is exactly the
original branch set. Hence no successful split is compatible with that
endpoint. With no split, all original positions remain the only logical
positions. Every original alpha must be changed to beta, which requires
its one successful promotion; no other successful promotion is enabled.
Thus $P_+=a,S_+=0$ pathwise. Taking the entry with all $m$ variable leaves
alpha proves the lower bound, and the deterministic all-$P$ traversal
proves attainability. Null nonterminating sets do not change the
expectation. $\square$

The prices in (AAII.27) concern permission to finish at different actual
endpoints. They are not a randomized improvement of Theorem 57.3 with
its deterministic quantifier, or of (AAII.30) with its fixed endpoint.
Nor is there pointwise disturbance dominance over all-$P$: on an all-beta
entry all-$P$ has zero successes, whereas mode zero can split every
variable leaf. In GLOBAL that event has probability $1-q$ and costs
$2m$ source vertices. In LOCAL it has positive probability
$(1-q)^m$. Thus an expectation improvement gives no smaller pathwise
worst-tape allocation bound. Requiring the actual source to remain the
entry is still stronger: monotonic source growth would forbid all
successes, contradicting Theorem 63.1's positive lower bound for
$v=1$ on this family.

## 65. Same-run traffic, randomness, material and continued use

**Definition 65.1 (actual parameters).** For the finite entry $t$ let
$a,b,L,n,D,D_\alpha$ have exactly the meanings in Definition 58.1, so
$L=a+b$, $n=2L-1$, and $D$ sums depths of all original logical nodes.
Let $b_V$ count eligible original beta leaves and put

$$
D_{\beta V}=\sum_{\substack{p\in F(t)\cap V_K\\t|_p=\beta}}|p|,
\qquad
D_s=\sum_{\text{successful acquisition targets }p}|p|.
\tag{AAII.31}
$$

Here $K$ is the actual original logical skeleton used only to state
counts, not supplied to the controller. On every reachable entry
$a+b_V=m$, while the other $L-m$ leaves are beta. All following
traffic counts concern that same actual run, not a normalized surrogate
or a different optimal run for each coordinate.

**Proposition 65.2 (literal acquisition account).** For GLOBAL and LOCAL,
on every terminating run,

$$
\begin{aligned}
\#\text{completed guards}&=n,&
G&=P_++S_+,&\Delta&=P_++2S_+,\\
I_{\rm acq}&=2D+4n,&
O_{\rm acq}&=5n+2D_s,\\
|C(t)|&=n+b,&|C(u_{\rm end})|&=n+b+\Delta,\\
\#\text{entry constructors}&=n,&
\#\text{current constructors}&=n+2S_+.
\end{aligned}
\tag{AAII.32}
$$

There are $n$ separate End/acknowledgement/Return cycles beyond those
literal bits. The two result words together have $4n+4S_+$ constructor
payload bits, on distinct owned backing. Acquisition makes $4\Delta$
located source-field assignments under AA Proposition 22.1's convention.
Under root-based navigation and parent-chain return it uses $D$ logical
child-link descents and $D$ parent-link ascents. In expectation,

$$
\begin{aligned}
\mathbb E G&=qa+(1-q)b_V,&
\mathbb E\Delta&=qa+2(1-q)b_V,\\
\mathbb E O_{\rm acq}&=5n+2qD_\alpha+2(1-q)D_{\beta V},\\
\mathbb E\#P\text{ attempts}&=n-L+qL,&
\mathbb E\#S\text{ attempts}&=(1-q)L.
\end{aligned}
\tag{AAII.33}
$$

Proof. Theorem 62.3 visits exactly the $n$ original nodes, including
branches, and no newborn node. Every original request has length
$2|p|+4$. Every reply has five bits plus $2|p|$ when it is a success,
by Definition 53.3, regardless of whether its kind is $P$ or $S$.
This proves the traffic sums. Original material has one vertex per
logical node and one marker per beta. Each success uses its original
one- or two-vertex template and only a split adds two logical nodes.
Two payload bits per constructor prove the code count. Those same
templates use four or eight source-field assignments. All targets are
original present positions; edits in other leaf cones do not change
their root depths or parent paths, proving the navigation counts.

There are exactly $L$ eligible original nodes: the root and the right
child of each of the $L-1$ original branches. This counts branches among
eligible nodes and is generally larger than $m$. Every other original
node is $L$-ending and receives $P$. At each eligible node the $P$
probability is $q$ in either implementation. Summing these marginals
proves the attempt counts. Only original alpha and eligible beta leaves
can succeed, with the probabilities in (AAII.29); weighting them by
address depths gives the expected reply count. $\square$

**Proposition 65.3 (separate randomness bills).** With Definition 62.1's
sampler, GLOBAL uses exactly one sampler invocation and LOCAL exactly
$L$ invocations. For $q\ne1/2$, the expected numbers of delivered fair
bits are respectively $2$ and $2L$; for $q=1/2$, the numbers are exactly
$1$ and $L$. Every individual terminating invocation uses its actual
finite number of bit-service calls, finite arithmetic and delivered
bits. Provider-call framing, acknowledgements and clearing are whatever
that separately supplied service actually requires; they are not
included in $I_{\rm acq},O_{\rm acq}$, which count the guard connection.

Proof. Eligibility is tested from the owned path before the guard reply,
so LOCAL samples even at an eligible branch. The count $L$ is proved in
Proposition 65.2. The geometric stopping calculation in Definition 62.1
and independence of fresh blocks in Theorem 62.3 give the claimed bit
expectations. The finite denominator and remainder bound give finite
arithmetic and bounded remainder storage per invocation. Bits may be
consumed and cleared; retaining their transcript instead has additional
backing and lifetime charges. GLOBAL retains its one mode through
acquisition, whereas LOCAL may clear a mode after its visit. The two
sampler bills therefore cannot be exchanged while retaining the claimed
endpoint law. $\square$

**Proposition 65.4 (old preparation and actual later successors).** The
old source preparation still has exactly $b$ successful promotions and
$L-1$ successful splits. Its initialization and successful edits use
$3+4b+8(L-1)$ located source-field assignments. Old addressed traffic,
allocation, grants and any retained old records are additional actual
resources, whether or not the observer can recover their serial order.
The acquisition assignments $4\Delta$ are added to this preparation.

For a subsequent completed continuation on the actual random endpoint,
let $r,z,p_+,s_+,J,J_+$ have precisely the meanings in Proposition 58.3.
Then its additional guard traffic and source growth are

$$
I_{\rm cont}=2J+4r+3z,\qquad
O_{\rm cont}=5r+2J_++3z,\qquad
\Delta_{\rm cont}=p_++2s_+.
\tag{AAII.34}
$$

At that settled cut the source has
$n+b+\Delta+p_++2s_+$ vertices. The current logical word has
$n+2S_++2s_+$ constructors and the immutable entry word has $n$.
Their total constructor payload is $4n+4S_++4s_+$ bits. Successful
continuation templates add $4p_++8s_+$ source-field assignments.
Every actual End, acknowledgement, Return, pending prefix, prediction,
code replacement, record copy and clearing is charged in addition.

Proof. The old counts are the same birth-type identities used in
Proposition 58.3; acquisition changes neither what was actually prepared
nor its charges. The continuation is the original complete parser and
source templates of Definition 53.3. Summing their literal lengths gives
(AAII.34), including absent, branch and wrong-type refusals among the
$r$ requests and the six unsupported tags among the $z$ requests.
Only splits add logical constructors, while both kinds add their actual
source vertices. The starting source is $u_{\rm end}$ from Theorem 62.3,
so substituting $\nu(t)$ instead would generally give a false source
count. $\square$

**Definition 65.5 (coexisting backing and optimization boundary).** If
$h$ is the original logical height, a single mutable path and ancestor
continuation flags use $O(h+1)$ symbols, in addition to the two result
words and actual request/reply buffers. Acquisition address/reply
payloads have width at most $2h+5$. No separate copied address for each
pending subtree is needed. The sampler adds its paid denominator,
$O(\log d)$ remainder state, mode and finite control; its bit provider
has its own binding and resources. Actual list links, result slots,
reference widths, source parent/left/right fields, rights, parser latches,
allocator state and instruction backing coexist with these payloads.
No address, grant or reference becomes free merely because its semantic
name is suppressed in the equations.

At a retained synchronized cut, paid finite current-code scans and word
replacement suffice for prediction and update. An implementation retaining
old and proposed current words and complete predicted and actual replies
pays for their simultaneous backing and cleanup. Copies or exports of
the entry/current words add their actual payload, framing and lifetime.
Computing a different view from the current code is further paid work.
The source material itself persists throughout. Almost-sure finiteness
is not a fixed lifetime store bound, an entropy-free hardware source,
a physical timing/energy theorem or an optimum of this complete resource
vector. Only the specified weighted source coordinate is minimized.

## 66. Earned initialization of full retained use and current four views

**Theorem 66.1 (the original complete task from either actual endpoint).**
For either acquisition of Theorem 62.3, the earned current word and
retained actual binding initialize Definition 55.1 with
$\widehat u=u=u_{\rm end}$, almost surely. From that cut, the same
predictor gives the entire original $Q_A$ of Definition 53.3, including
exact replies, enabledness and all settled source successors for every
finite common adaptive continuation. Forwarding the requests actually
uses that same source and reestablishes the current-code invariant after
each completed return. The entry archive remains separately available.
This assertion applies to each realized endpoint, not merely to its
mean, a mixture code or the deterministic endpoint $\nu(t)$.

Proof. Theorem 62.3 establishes the initial equality using actual
responses and actual edits; it does not posit a code for an unknown
source. For the inductive step, suppose the equality holds at a settled
cut. Logical code navigation and actual navigation agree along the
requested address until reaching the corresponding constructor or
blocking at the same logical leaf. Neither follows a material beta
marker. Therefore all four target rows of Definition 53.3 agree,
including absent, branch and wrong-type refusal reasons. On success,
the predicted kind and address in the entire Growth frame are the
actual kind and address, and the prescribed code replacement is exactly
the actual source's logical replacement. The real retained target and
reused/fresh source vertices are supplied by the source operation, not
by the predictor's abstract word construction.

Each of the six other request tags returns its complete BadFrame reply
and preserves both codes and source. A proper incomplete address frame
retains its actual input prefix and waits, with no invented completed
reply or committed successor; any finite completion returns to the
complete-frame case. The actual call consumes the whole printed answer,
End, local acknowledgement and Return, and commits its backed code edit
before the next synchronized cut. Finite scans and replacements terminate
on finite words, and the unchanged rights, serialization and material
premises enable the real operation. This is precisely the induction of
Theorem 55.2, whose inductive step needs equality of the current code,
not the special form $\nu(t)$ of its earlier initialization.

Induction on the number of completed requests covers common adaptive
policies, since equal full replies give the same subsequent choices.
Fixing any common later random choices gives the same induction; the
claim therefore also covers such policies. No arbitrary busy-state
identification, source reset, hypothetical authority or source-dependent
selector is introduced. The actual callable binding and current rights
are retained premises distinct from the computed predictive content.
$\square$

**Theorem 66.2 (supplied inverse on the actual current image).** At every
synchronized cut of Theorem 66.1, let $u$ be the actual reachable current
term. Select the same four independently meaningful current contents
as Definition 56.1, with the fixed binding and authority as common
context:

| View | Exact selected content on this source |
| --- | --- |
| Space | Rooted oriented material-address support of $C(u)$, excluding observer-record edges |
| Boundary | Terminal-material-address antichain of that $C(u)$, including unary beta markers |
| Time | Labelled causal successful-source-event order $E(u)$ of AA Definition 17.1 |
| Memory | Actually retained current constructor word, with retained callable binding and current rights |

On their exact reachable images these contents mutually recover one
another by the supplied AA §17 and AAII Theorem 56.2 maps. All routes
agree and commute with every completed original $Q_A$ request, its full
reply and its settled source successor. Their task kernel is exactly
equality of $u$, with this common context fixed.

Proof. Source operations preserve reachability in $\mathcal D$.
Material prefix closure converts Boundary to Space, and maximal material
addresses convert Space to Boundary. Arity parsing of valid $C(u)$
decodes terminal alpha, unary beta and binary branch, so either recovers
$u$. At a beta logical leaf $p$ its material terminal address is $pL$;
at an alpha it is $p$. Omitting those unary markers would change this
inverse and is not allowed.

For Time, AA Theorem 17.2 uses the labelled membership of splits and
promotions, and their causal dependencies. Children are born from their
parent split. A position is a branch exactly when its split is present;
a remaining leaf is beta exactly when born beta or promoted, otherwise
alpha. Conversely $u$ specifies precisely those events and the supplied
causal edges. This reconstructs the causal order, not an old serial
extension, the acquisition bit choices or failed-call chronology.
Memory parses to $u$ by Theorem 66.1, and encoding a recovered $u$ gives
its current constructor content. Such re-encoding does not recover
private backing names or create the supplied authority.

All conversions thus decode and re-encode the same $u$ on actual images.
Their inverse and triangle identities follow there. Theorem 66.1 gives
the same complete reply and actual logical successor $u'$ for each
completed operation. A success adds exactly its actual labelled event
and applies the corresponding source template; refusals and BadFrame
preserve the selected contents. Reapplying the supplied maps to $u'$
gives the same updated view along every route, proving commutation.
For task separation, take the first differing constructor of unequal
ordered terms after descending through common branches. Its position
is present in both. A single original $P$ there gives respectively
Growth, wrong-type refusal or branch refusal for alpha, beta or branch.
Thus unequal terms are $Q_A$-distinguishable without a Tag port, while
equal terms have the entire same task by the preceding induction.
$\square$

**Proposition 66.3 (current representation, archive and provenance).**
The current inverse supplies neither the immutable entry archive nor
unobserved old serial history in general. Already entry alpha followed
by its successful $P$, and entry beta followed by a refused $P$, have
the same actual current beta content. Both occur in GLOBAL's mode one
and in the corresponding positive-probability LOCAL mode. Their entry
codes and acquisition responses differ. Therefore no function of these
current contents alone recovers the entry archive on that image.

The actual archive is nevertheless earned and retained by Theorem 62.3.
Likewise an actual current causal view, a representation computed from
that archive/current word, and an observed record of old provenance are
three different access claims. The supplied conversion computes the
selected current content; it adds no raw Space, Time or Boundary read
port and no observation of old serialization, routing ranks, refusals,
provider state, private references or full authority bytes. Authority
and binding remain common supplied context in Theorem 66.2. If an
observer is additionally allowed to inspect the entry archive, RNG
transcript or private work, that enlarges the task and requires views
supplemented with the newly selected information. $\square$

## 67. Supplier correspondence and exact applicability boundary

**Definition 67.1 (mathematical suppliers).** The weighted guard-price
result (AAII.27), its two actual acquisitions and their earned interface
application are `repo-derived` in the explicitly extended installation
of Definition 61.1. Their new source-relative content is the randomized
weighted acquisition price and its endpoint/resource distinction.
The following existing results retain their own hypotheses and supply
the indicated parts; no general syntax, random generation or causal
inversion novelty is claimed.

| Supplier | Applied content and boundary |
| --- | --- |
| [AA §§17,20–23](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction), AAII §§53–59 | The exact reachable leaf constraint, material markers, causal event membership, original local source edits, full guard frames, no-indirect-leaf-read lemma, traversal backing, retained predictor induction and current inverse are reused. The deterministic bound does not itself quantify randomized expected fees. |
| [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | `native_source_producer` and its private traversal/read-count/stationarity suppliers use a nondestructive four-valued Native read. That read is unavailable here. Its source-independent backed traversal is a supplier pattern, not a guard-only acquisition theorem. |
| [NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean) and [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs) | Given-code tree views, child navigation and finite walk/readout helpers operate after syntax is supplied. Theorem 62.3 earns that syntax from actual guards rather than assuming it. |
| Pinned mathlib [Algebra/Free.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Free.lean) | `FreeMagma.of`, multiplication and `lift` supply ordinary ordered binary syntax and its fold. A fold supplies no unknown-source observation, rights or sampler. |
| Lumbroso, [*Optimal Discrete Uniform Generation from Coin Flips, and Applications*, Appendix B](https://arxiv.org/abs/1304.1916v1) | The classical rational Bernoulli digit/geometric-index construction supplies exact almost-sure-finite sampling with mean two delivered bits and bounded remainder storage. The direct fair-bit special case is charged separately. No general optimal-random-bit claim is imported. |
| [NativeMaterialRootRecognition](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.lean) and [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.scribe.cs) | Root recognition uses a supplied finite full graph and complete ordered terminal data, under its leaf hypotheses. Those inputs are not exposed by the present guard-only port. It neither supplies the missing entry code for this task nor changes the paired-leaf lower bound. |
| [Unknown-field startup §§24–26](RECURSIVE_RELATIONAL_OBSERVATION_UNKNOWN_FIELD_NATIVE_STARTUP.md#24-arbitrarily-small-signed-entry-fields-can-conceal-a-longer-native-path), AAII §60 | The published small-signed-entry obstruction has its own unknown rational path/Jacobi observation domain, including its zero-error random finite-prefix argument. The published history floor uses known-alpha full-history acquisition and conditional old-order payloads. Neither is this finite LAB variable-leaf fee theorem; their obstructions and history scopes are unchanged. |
| [Uncalibrated quadratic-clock private randomization §7](FIB_UNCALIBRATED_QUADRATIC_CLOCK_PRIVATE_RANDOMIZATION.md) | Its fixed complete real clock worlds, report choices and expected origin error define a different randomized decision problem. No operational map identifies those worlds or reports with addressed LAB guards, irreversible leaf edits and exact entry output. |
| [SharedEnergyCompactAction](../../../D5/S3/Quantum/Fibers/SharedEnergyCompactAction.lean), [SharedEnergyCopyThreshold](../../../D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.lean), [EffectProbabilityExtension](../../../D5/S3/Quantum/Foundation/EffectProbabilityExtension.lean) | Compact matrix-group/Haar moments, shared-energy density-state relations and finitely additive effect-probability extension have their declared matrix/effect inputs. They provide neither this guard attachment nor an independent fair-bit provider or unknown-entry decoder. Similar randomness or representation vocabulary is not an operational bridge. |

The current four-view result is an application of the already supplied
inverse, not another causal-reconstruction theorem. Elementary pairing,
finite averaging and nonnegative expectation in Theorem 63.1 are proved
there directly; no unverified minimax interchange is invoked. The
supplier comparison is relative to these specified sources and their
hypotheses and makes no worldwide originality or Lean-certification
claim for this prose unit.

**Definition 67.2 (remaining model and programme boundaries).** All
claims require the genuine known-alpha LAB source origin, unknown entry
in $\mathcal D$, authentic guard-only attachment, source-independent
paid randomness, current exclusive rights, serial completion, unchanged
source orientation and sufficient actual finite backing. Timing leaks,
observable quotas, concurrent changes, revocation, interruption, extra
nondestructive readouts or source-correlated random bits change the
competitor class. Providing an entry table, a terminal roster, a full
material graph or a generation history would be an extra input rather
than an acquisition established here.

The expected source optimum is for exact entry acquisition while allowing
the changed endpoint of (AAII.26); fixed normalization retains (AAII.30).
It supplies no joint optimum of growth, allocation, random bits, guard
traffic, code layout, references, grants, work, lifetime, timing or energy.
The independently supplied random provider is not derived from a quantum
or field inverse. Richer prepared quantum/field four-view services retain
their own installed ports, positivity/effect assumptions and actual-image
conditions; they do not install this provider or justify a common source
across models.

The full known-alpha seven-request $Q_g$ and its source-paid historical
records remain the separate services of AAII §§47–52 and §60. Earned
current syntax does not reconstruct erased old order, old routing words
or their unavailable rights. Every original fixed-$G_{\rm gc}$,
original-$Q$, parked-consumer, unchanged-initialization, terminal and
final-no-Ready statement retains its exact source and interface scope.
No universal native-LAB/path realization, physical origin theorem,
independently acquired full authority/provenance or full common-process
four-expression/resource-minimality conclusion follows. Those broader
obligations remain unresolved by this bounded conditional theory.

## 追加锚（本行以下为增补区）

## 68. A recoverable source encoding on the original LAB attachment

**Definition 68.1 (source, acquisition task and represented task).**
Use exactly the LAB source of AA Definitions 17.1 and 17.3 and the
minimal guard attachment of Assumption 53.2. Thus the actual source was
prepared from a known allocated alpha root by a finite legal word of
addressed promotions and splits. Its unknown entry is any
$t\in\mathcal D$, where no alpha leaf has an $L$-ending logical address.
The observer initially has no source-dependent word, roster, size,
generation record or response table. It has the authentic opaque callable
root, its original orientation, current exclusive $P/S$ rights, complete
reply/return connection, source-independent finite code and sufficient
owned finite backing for each execution claimed. Only complete guard
replies reveal source-dependent information. Logical addresses stop at
logical leaves; a beta's terminal material marker is not a logical child.

Calls, observer updates and the later outer service are serialized. There
is no crash, interrupt, revocation, concurrent writer, autonomous growth,
observable quota, allocation-name inspection, duration readout, Tag,
Native Read, field, reset or cloning port. Rights and binding are supplied
premises, not conclusions learned from guard answers. Retention,
communication, allocation, local computation and clearing remain paid.
The acquisition must earn the exact entry code and an actual advanced
endpoint on this same source. Subsequent use will have the explicitly
represented interface $Q_J$ of §70, distinct from applying the original
$Q_A$ directly to the advanced physical term. Neither interface includes
the seven-request history task $Q_g$ of §§47–52.

**Definition 68.2 (encoding and recognized range).** For finite ordered
LAB terms define

$$
J(\alpha)=\alpha,\qquad J(\beta)=\langle\beta,\alpha\rangle,
\qquad J(\langle u,v\rangle)=\langle J(u),J(v)\rangle.
$$

Let $\mathcal R$ be the least finite-term grammar

$$
r::=\alpha\ \mid\ \langle\beta,\alpha\rangle\ \mid\ \langle r,r\rangle.
$$

Define a partial decoder $K$ as follows. At alpha return alpha. At the
literal pair $\langle\beta,\alpha\rangle$ return beta. At any other pair,
recursively decode both children and return their ordered pair, provided
both decodings succeed. Reject bare beta and every unsuccessful recursive
case. This is a finite structural procedure on an owned constructor word,
not a new source primitive. No member of $\mathcal R$ has root beta;
therefore the literal sentinel pair cannot also be a pair of two members
of $\mathcal R$. In particular the two pair rules are unambiguous.

**Lemma 68.3 (two round trips and exact birth-typed image).** On all finite
terms, $K(J(u))=u$. The domain of successful $K$ is exactly $\mathcal R$,
and $J(K(r))=r$ for every $r\in\mathcal R$. Consequently $J$ is injective,
and its exact image on reachable LAB entries is

$$
\mathcal I:=J[\mathcal D]=\mathcal R\cap\mathcal D.
$$

Proof. Every encoded term has root alpha or branch. For a leaf alpha the
first round trip is the first rule. For beta it is the sentinel rule.
For an original branch, both encoded children have root different from
beta, so the encoded branch cannot be the sentinel. The recursive rule
and the two induction hypotheses return the original branch. This proves
the first round trip by structural induction.

Induct on a successful decoder computation. Its alpha case lies in the
first range rule, its sentinel case in the second, and its recursive pair
case in the third by the induction hypotheses. Conversely induction on
the range grammar gives a successful computation: in its third case the
left child has root different from beta, so the sentinel case does not
interfere. The same induction proves the second round trip. Applying
$K$ to an equality of encoded terms proves injectivity.

Encoding preserves every original alpha leaf at its original address.
The only added alpha leaves are the right children of original beta
leaves. Hence an $L$-ending alpha in $J(u)$ exists exactly when one existed
in $u$. For the reverse implication, an $L$-ending alpha in $u$ persists;
for the forward implication, any new alpha ends in $R$. Thus
$u\in\mathcal D$ if and only if $J(u)\in\mathcal D$. Every $J(u)$ lies in
$\mathcal R$. If $r\in\mathcal R\cap\mathcal D$, put $u=K(r)$; then
$J(u)=r$, and the just-proved equivalence gives $u\in\mathcal D$.
This proves the displayed image equality, including the singleton entry
alpha. $\square$

The encoding is not FARG's simultaneous substitution $\rho$: in
particular $J(\alpha)=\alpha$ whereas $\rho(\alpha)=\beta$.
The round trips are ordinary syntax facts. Their use below requires an
actual guard execution reaching $J(t)$ and an earned word for $t$.
A syntax inverse by itself supplies neither that execution nor a guard
observation of an unknown entry.

## 69. Actual guard acquisition of an encoded endpoint

**Definition 69.1 (the split sweep).** Begin with empty logical address
and empty ancestor-continuation stack. At a scheduled address $p$, send
one complete original $S_p$ frame, consume its complete reply and finish
its return. Refusal(wrong type) records alpha and finishes this visit.
Growth$(S,p)$ records beta and finishes this visit: do not schedule either
newborn child. Refusal(branch) records a branch, visits its left child,
then its right child, using a backed pending-right flag. Stop when the
root visit and every pending continuation are finished. An absent refusal
is outside the promised executions and is not interpreted as a leaf.

The output is Definition 54.1's canonical preorder word, with two-bit
symbols $00,01,10$ for alpha, beta and branch. Retain one mutable address,
a finite flag per active ancestor, the growing output word and the actual
bound root/rights. Scheduling and parsing use only acquired replies, not
a supplied subtree, fuel, height or stopping bound. The stack program is
source independent; its actual stack and output are not bounded in size
by finiteness of that program. This is the entry-node traversal technique
of §§54 and 62, with a different leaf operation and endpoint.

**Theorem 69.2 (earned entry, exact source and termination).** For every
$t\in\mathcal D$, every legal old LAB preparation ending at $t$, and every
installation of Definition 68.1, the split sweep terminates with an owned
canonical word for $t$ and actual physical source $J(t)$ on the same
callable root and current authority. It visits exactly the entry logical
positions, once each in preorder. Its only successful source events are
one split at every entry beta leaf. Its acquisition endpoints, as the
entry varies, are exactly $\mathcal I$.

Proof. At the start of any scheduled entry-subtree visit, all previous
edits are in finished entry-leaf cones, disjoint from the pending subtree.
A previously split entry leaf has newborn descendants, but the controller
has finished that visit and never schedules them. A pending child is
scheduled only after its actual parent produced a branch refusal. Thus
all scheduled positions exist and their constructors still equal the
entry constructors. This invariant is preserved by every scheduling
step and source edit.

Prove the visit assertion by induction on the finite entry subtree,
allowing arbitrary pending continuations outside its cone. At alpha the
actual split has the wrong type; it leaves alpha and records alpha.
At beta the actual split succeeds, leaves the pair beta-alpha and records
beta. The visit ends in both cases, so neither case uses a newborn child
as evidence about the entry. At a branch the actual refusal preserves
both child cones. Apply the left induction hypothesis and then the right
one; disjointness preserves each hypothesis. Their recorded words form
the original branch word, and their physical endpoints form the pair of
encoded children. These are precisely the three clauses of $J$.

Every actual request, reply, End, acknowledgement, return and finite local
update completes under the installation premises. The structural induction
establishes finitely many visits and stack operations without passing a
runtime bound to the observer. It also excludes absent replies. At the
root completion the output is therefore the exact entry word and the
physical endpoint is $J(t)$. The current representation needed by §70 is
this earned word $t$; a second physical-current word $J(t)$ need not be
retained. The real reference, rights, program and work backing remain
owned for later use. Every endpoint belongs to $\mathcal I$ by Lemma
68.3, and each member of that set is obtained from its decoded reachable
entry by this same sweep. $\square$

**Definition 69.3 (retained-use invariant).** At an outer Ready cut retain
one valid live word $v$, the same callable source root and its current
exclusive authority, the framing/adapter program, and owned pending,
answer and work backing. The invariant is that the actual physical term
is $J(v)$. The word is initially the acquired $t$, not a supplied response
oracle. Retaining it as live mutable state gives no separate immutable
entry archive: after later represented edits, an old entry report requires
its own retained copy or the restricted reaccess experiment of §72.

## 70. The complete represented continuation on the same source

**Definition 70.1 (outer frames, replies and real macros).** $Q_J$ uses
exactly Definition 53.3's framing and complete reply alphabet, evaluated
on the represented term $v$. In particular its addressed request length
is $2|p|+4$, a Growth reply has length $2|p|+5$, and any of the three
Refusal reasons has length five. Logical lookup in the earned live word
uses the original blocking rule: a strict extension through a leaf is
absent. The complete semantic table is

| Represented target at $p$ | Outer $P_p$ | Outer $S_p$ |
| --- | --- | --- |
| absent | Refusal(absent), identity | Refusal(absent), identity |
| branch | Refusal(branch), identity | Refusal(branch), identity |
| alpha | Growth$(P,p)$, replace by beta | Refusal(wrong type), identity |
| beta | Refusal(wrong type), identity | Growth$(S,p)$, replace by pair beta-alpha |

For a represented successful $P_p$, the adapter actually calls $P_p$,
consumes its complete reply/return, then actually calls $S_p$ and consumes
that complete reply/return. For a represented successful $S_p$, it
actually calls $S_{pL}$ and consumes its complete reply/return. Here $pL$
is the left logical beta of the physical sentinel pair $J(\beta)$;
it is not the unaddressable material marker of an unsplit beta. The
adapter checks the expected complete inner successes before committing.
A predicted refusal requires no source edit or inner call and returns
its exact outer reason. The other six three-bit tags are complete
unsupported frames returning the three-bit BadFrame and identity
successor. They do not call a missing service. A proper unfinished $P/S$
address frame waits, retains its received input and has no completed reply.
Exactly one frame is consumed per outer transaction. The outer client
calls an actual owned adapter entry, whose stored reference is bound to
the original dispatcher. Both that outer connection and the inner callable
reference, current grants and input/output backing are retained and paid;
the represented word does not stand in for either callable binding.

Receive backs every accepted outer bit before releasing its latch. Before
a successful macro the adapter owns the old word, parsed address, operation,
phase, proposed successor word and sufficient finite backing/authority
for the entire macro and reply. Only the permitted real source templates
allocate source vertices; the adapter installs no new source opcode.
Between the two inner calls of a represented promotion the outer service
remains busy even though the original dispatcher has returned. After the
last inner return, commit the new live word, seal the entire outer answer,
Print all its bits and End, consume the local acknowledgement, then Return
and clear finite scratch before Ready. The root, current authority and
live word survive cleanup. No next outer frame is admitted while busy.
The real source calls, their traffic, retained intermediate data and the
outer traffic are all actual operations with separate costs.

**Theorem 70.2 (full successor correspondence and continued use).**
Starting at any Ready cut satisfying Definition 69.3, Definition 70.1
implements the complete $Q_A$ table on $v$ through $Q_J$. It returns
exactly the displayed outer replies and preserves the invariant with
$v$ replaced by the displayed represented successor. The same assertion
holds for every finite common adaptive continuation of full frames,
including refusals and unsupported tags, and for finite extensions of
pending prefixes. Enabledness is conditional on the same current rights,
serialized phase, backing and acknowledgement assumptions as above.

Proof. At any logical position of $v$ above its leaves, $J$ retains the
same branch context and address. Thus a represented alpha at $p$ is an
actual alpha there. The first real call promotes it to beta; the second
splits that beta. The net replacement is $J(\beta)$, so, writing $P_pv$
for the represented successful successor,

$$
S_p(P_p(J(v)))=J(P_pv).
$$

At a represented beta at $p$, the physical cone is
$\langle\beta,\alpha\rangle$. Splitting its actual left logical beta
gives $\langle\langle\beta,\alpha\rangle,\alpha\rangle$, which is
$J(\langle\beta,\alpha\rangle)$. Consequently

$$
S_{pL}(J(v))=J(S_pv).
$$

In both equations the operations are real legal source changes at the
stated original-root addresses. Context replacement outside that cone
commutes with $J$ by its branch clause. These arguments prove actual
success and the proposed code update; they assume neither a raw read
port nor an inverse source edit.

For every negative case, finite lookup in the already earned exact word
gives precisely the represented absent, branch or wrong-type case.
Returning that reason with no inner edit preserves $J(v)$. The fixed
unsupported reply and the unchanged source are also exact. Both parsers
use the stated finite prefix grammar, so a proper partial frame has the
same waiting condition and every completed extension enters the proper
case. Actual input backing, full answer construction, End, acknowledgement,
return and cleanup ensure that equality concerns whole replies and settled
successors, rather than just an initial response bit. Missing rights or
wrong phase disable a call; they are not reclassified as a leaf refusal.

Induct on complete outer transactions. The induction hypothesis supplies
the word/source invariant for the next chosen frame; the one-step argument
returns the same whole reply and the next invariant. An adaptive client
therefore makes the same next selection from the same replies. Finite
prefix extensions follow the same parser transition rule. This proves
all claimed finite continuations and actual retained callable use.
$\square$

**Proposition 70.3 (exact returned image and interface distinction).**
Across all promised acquisitions and completed $Q_J$ continuations the
physical returned image is exactly $\mathcal I$. For fixed acquired entry
$t$, it is exactly $J[\operatorname{Desc}(t)]$, where
$\operatorname{Desc}(t)$ comprises the finite legal LAB successors of $t$,
including $t$ itself. These assertions do not extend the inverse to every
intermediate physical cut and do not equate $Q_J$ with raw $Q_A$ on $J(v)$.

Proof. Every represented success is an ordinary LAB successor of $v$;
refusals and unsupported requests preserve it. Conversely every finite
legal successor word is realized by the corresponding successful outer
frames by Theorem 70.2. This gives the fixed-entry equality. Taking all
entries includes every $J(t)$ already at acquisition return and adds no
term outside $J[\mathcal D]$, proving the global equality.

For $v=\alpha$, a successful outer promotion has the actual intermediate
term beta after its first inner return. Bare beta is outside $\mathcal R$,
so $K$ is undefined there. There is no outer Ready cut at that point.
For $v=\beta$, outer $P_\varepsilon$ returns wrong type; raw
$P_\varepsilon$ on the physical $J(v)$ returns branch. The two interfaces
therefore have different replies on the same physical source. The
proved correspondence concerns the adapter's outer interface and full
return, not a client bypassing it, arbitrary interruptions or raw busy
states. $\square$

## 71. Independently meaningful views on synchronized returned cuts

**Definition 71.1 (four data meanings and their exact domains).** Fix the
actual opaque root binding, orientation, current authority and the
source/adapter contract. At a synchronized outer Ready cut with physical
term $u=J(v)\in\mathcal I$, define the following data using the original
source meanings of AA §17:

| View | Independently specified content |
| --- | --- |
| Space | Actual material address support $S_0(C(u))$, with source edges only |
| Boundary | Actual terminal-material address antichain $B_0(C(u))$, including beta markers |
| Time | Actual labelled successful-source causal lifecycle order $E(u)$ of AA Definition 17.1 |
| Memory | The acquired live canonical word $v$ at the retained callable entry |

Time records event membership, addresses, kinds and causal precedence.
It does not record a chosen total serial order, refusals, communication,
controller scheduling or macro boundaries. Space and Boundary do not
include private record edges. Memory is an actually acquired current word;
it is not a copy of the whole preparation or outer transcript. The common
binding/authority context is retained actual material, not secretly part
of the tree data or something any data conversion manufactures.
For each view its domain below is precisely its image as $v$ ranges over
$\mathcal D$, or the restriction to $\operatorname{Desc}(t)$ after a fixed
entry. Arbitrary finite supports, arbitrary antichains or arbitrary
labelled orders outside these images are not claimed to have inverses.

**Theorem 71.2 (four-way recovery, route agreement and task kernel).**
On these exact domains each view recovers the same represented term $v$
and the actual physical term $u=J(v)$, and hence all the other three
contents. All conversion routes agree. Their equality kernels are
exactly equality of $v$, which is also the complete represented
continuation kernel of $Q_J$ at the fixed binding and authority. These
recoveries are finite procedures on given owned data. The acquisition
installs the Memory-based callable service; it does not install three
additional source read ports.

Proof. Apply the existing AA Theorem 17.2 and Definition 17.3 to the
actual reachable term $u$. Their original arity parser takes material
support to $u$; prefix closure takes the terminal antichain to that
support; event membership and the specified birth types take the actual
causal order to $u$. These are the supplied original inverses, with
parameter exactly $u=J(v)$, rather than new tree-inverse theorems. Apply
$K$ to the resulting term. Lemma 68.3 gives $K(u)=v$. Memory parses its
own canonical word to $v$ and computes $J(v)=u$. Conversely $v$ computes
$u$, its material support and terminals, and its labelled causal order
by the supplied finite definitions. Thus every conversion is the
appropriate observation after recovery of this same $v$; both round
trips hold and every composed route agrees on its actual image.

Equal $v$ gives the same complete outer task by Theorem 70.2. For distinct
$v,w$, descend through their common branch constructors to their first
differing constructor. The address is present in both. The outer promotion
there distinguishes alpha, beta and branch respectively by Growth,
wrong-type refusal and branch refusal. Hence the complete tasks differ.
The view round trips give precisely the same equality kernel.

All these algorithms parse finite data, construct finite trees or event
lists and run the given decoder. Their inputs and outputs require owned
backing and ordinary computation. Computing a boundary or event order
from the acquired word is a description of the actual source content;
it is not an observation of previously unexposed serial provenance.
Neither a correct word nor a conversion creates a reference, root
association or grant. Those remain the common genuine attachment used
by the real calls. $\square$

**Theorem 71.3 (dynamics compatibility at the declared cuts).** For every
complete $Q_J$ transaction between synchronized outer Ready cuts, all four
recovered dynamics agree with the represented successor table. This also
holds for every finite composite of such transactions. Time's physical
update contains two successful LAB events for a represented promotion and
one event at $pL$ for a represented split.

Proof. By Theorem 70.2 the physical endpoint is the encoding of exactly
the next represented word. Each final view is its independently specified
observation in Definition 71.1. Recovering before or after applying that
observation therefore gives the same next word by Theorem 71.2. For
Time, the actual calls add $P_p,S_p$ or $S_{pL}$, with their actual
local/creation precedences; they do not add a single fictitious event
at the virtual address in place of those real events. Negative cases
add no successful-source event. This verifies compatibility also for
that view. Induction gives the finite-composite statement. Intermediate
inner returns need not lie in the image, as Proposition 70.3 exhibits.
Private pending words, answer buffers, allocation identities and full
control phases are outside the claimed view inverse even at cuts where
the physical term happens to lie in the image. $\square$

## 72. Paid clearing and one advancing reaccess

**Definition 72.1 (the cleared receiver experiment).** Immediately after
Theorem 69.2, hold the actual source at $J(t)$, admit no represented
continuation, and perform a paid clearing of the receiver's entire
accessible entry-dependent information. This includes live/entry/current
words, caches, reply transcripts, stack, pending input/output and proposed
words, exported copies or callable archives available to this receiver,
and any accessible length, layout or metadata that would disclose them.
The receiver retains only common finite code, the opaque actual root,
current exclusive rights, their source-independent I/O/adapter connections,
and a fixed public stage flag selecting this second sweep. There is no
source-correlated auxiliary provider or future input. The source itself
is not cleared.

The experiment requires actual clearing authority over these records;
if an accessible external copy cannot be cleared, it is not an instance
of this experiment. One realization exports no retained copy and overwrites
its owned used records, resets list heads/counters to the common empty
state, and leaves no accessible record of old lengths. Retained arena
capacity, inaccessible reclaimed backing and their clearing work still
count as actual material/work. As in Assumption 53.2, occupancy, allocator
names, duration and resource amounts are not observation channels.
No claim is made of erasing all past information elsewhere in the world.
The second receiver starts without an entry-dependent word but with
sufficient finite paid backing for its actual new execution.

**Theorem 72.2 (source-resident recovery with the correct new predictor).**
For every $t\in\mathcal D$ in the experiment of Definition 72.1, a second
split sweep earns an owned word $w=J(t)$ and leaves the same actual source
at $J^2(t)$. One subsequent paid application of $K$ to $w$ returns the
original entry $t$, without using any cleared word or transcript. The
legitimate live predictor for further ordinary $Q_J$ use is $w=J(t)$.
When $t$ has a beta, the separately decoded $t$ cannot be used directly
as that live word. For the degenerate entry alpha the two words coincide.

Proof. Lemma 68.3 places $J(t)$ in $\mathcal D$. The new receiver has
exactly the empty-source-dependent-record entrance required by Theorem
69.2, now with actual entry $J(t)$ and the same genuine attachment.
That theorem therefore earns its exact entry $w=J(t)$ and changes the
source to $J(J(t))$. Lemma 68.3 gives $K(w)=t$ by a finite computation on
this newly earned word. The computation has no access to cleared data.
Injectivity of $J$ identifies the original entry in this declared image;
the distinction survived in the source rather than in an assumed archive.

At the new returned cut the invariant of Definition 69.3 is physical
source $J(w)$ with live word $w$. Using $t$ directly in that same predictor
would instead represent source $J(t)$. If $t$ has a beta, encoding strictly
increases its node count, so $J(t)\ne t$ and injectivity gives
$J^2(t)\ne J(t)$: the proposed direct use has the wrong invariant.
For the reachable entry with no beta, namely alpha, both words coincide.
One may instead compute $J(t)$ anew from the decoded result, paying the
computation and backing to restore the correct live word. Keeping $w$
while constructing a separate result $t$ uses both words concurrently;
that retention and the decode are paid. The reference and current rights
are never inferred from either word and remain the authentic retained
ones. $\square$

This is a one-reaccess source-transforming experiment: both sweeps split
each beta present at their respective entry. When the original entry
has a beta, the second sweep strictly adds source material. The reachable
degenerate entry alpha has no beta and is fixed by $J$. The result is
neither stationary retrieval nor source restoration. If represented
continuation precedes the clearing, the same construction recovers that
then-current represented word $v$ from $J(v)$; it does not identify the
original $t$ without a separately justified version record. No arbitrary
old-history recovery or indefinite immutable archive service is asserted.

**Proposition 72.3 (precise gain over destructive normalization).**
The source-resident distinction of Theorem 72.2 is absent from the
normalization $\nu$ of §54 on each of its nontrivial fixed-skeleton leaf
fibres. If all other accessible distinctions are genuinely cleared, a
common deterministic future guard controller cannot recover every entry
in such a fibre from the normalized source. This comparison concerns
entry recovery after clearing, not the full resource optimality of either
procedure.

Proof. On a fixed ordered skeleton, fix all forced left-ending beta
leaves and vary $m$ eligible root/right-ending leaf labels. These give
$2^m$ reachable entries and the same actual normalized term: $\nu$ makes
every leaf beta. With common attachment, authority, cleared accessible
state and future input, the next actual guard reply is the same in all
these worlds. The resulting source and receiver states remain equal
modulo opaque fresh-name spelling. Induction gives the same complete
finite future, so an exact different entry answer in every world is
impossible. This is the fibre/pigeonhole obstruction already used in
§§57 and 59; in particular a fixed-width accessible supplement resolving
this fibre would require at least $m$ bits. No new general information
lower bound is needed here.

In contrast $J$ is injective on this fibre and Theorem 72.2 supplies an
actual guard-only second acquisition and decoder. Merely deleting the
second of two private words from the normalization procedure would not
supply this property: an uncleared entry word already computes its
normalized endpoint, whereas the stated comparison clears that word as
well. Neither procedure's distinct endpoint or continuation interface
can be substituted into a fixed-endpoint/original-interface optimum.
$\square$

## 73. One-run material, traffic, work and retention account

**Definition 73.1 (coordinates and charging convention).** For the actual
entry $t$ write $a,b$ for its alpha and beta leaf counts, $L=a+b$ for its
leaf count, $n=2L-1$ for its number of logical nodes, and $h$ for its
logical height. Put

$$
D=\sum_{p\in\mathcal L(t)}|p|,\qquad
D_\beta=\sum_{p\text{ a beta leaf of }t}|p|,
\qquad N=n+b.
$$

Here $\mathcal L(t)$ includes all logical positions; $N$ is the initial
material vertex count, including beta markers. Count request and reply
payload bits in Definition 53.3's fixed framing. Count End,
acknowledgement, return and cleanup separately; payload lengths alone
are not the communication protocol. Source structural assignments use
AA §22's original three-reference-field representation: four assignments
per promotion and eight per split, besides actual cursor, allocation,
grant, observer and communication operations. Every literal reference
or numerical operand pays its actual representation width.

Old preparation is part of this same source's cost. Its legal successful
event word has $b$ promotions and $L-1$ splits, hence
$3+4b+8(L-1)$ source structural assignments including root initialization.
If $e=b+L-1$ and $H$ is that word's sum of event-address depths, its
addressed request/reply payloads are $2H+4e$ and $2H+5e$, with $e$ full
completion cycles. Any additional producer activity is additional actual
cost. The old word is not supplied as an observer input. Root allocation,
producer control, actual references/grants, attachment, old I/O/backing
and any genuinely retained old records remain charged.

**Theorem 73.2 (first sweep and retained live word).** The first sweep
makes exactly $n$ split calls, of which $b$ succeed. It makes no promotion
call, adds $2b$ material vertices, and ends with $N+2b$ source vertices.
Its addressed payloads are

$$
I_1=2D+4n,\qquad O_1=5n+2D_\beta.
$$

There are $n$ full End/acknowledgement/return cycles, $D$ source-navigation
descents and $D$ ascents when each call returns along the parent chain,
and $8b$ source structural assignments. Its live word has $2n$ constructor
content bits. These statements hold simultaneously on the run of Theorem
69.2 and do not include the additional backing listed below.

Proof. Theorem 69.2 visits each entry logical position exactly once,
with success exactly at its beta leaves. Each success adds two vertices.
Every request at depth $d$ has $2d+4$ bits. A success reply has $2d+5$
bits and every refusal has five. Summing separately over all positions
and successful leaves gives the two payload formulas and completion
count. Each navigation uses its entry depth, giving $D$ in each direction.
The original split template gives $8b$ assignments. Two bits per visited
constructor give $2n$. No read-free synthesis or preliminary traversal
has been added to these counts. $\square$

An attained observer implementation uses a linked mutable address, backed
ancestor flags and a tail-appended constructor word. Scheduling appends
and deletes each entry-tree edge once and changes $O(n)$ flags. Formatting
addresses, consuming replies and constructing the output use
$O(n+D)$ symbol operations in addition to source navigation. The address
and flags have $O(h+1)$ symbols at peak; their links, literal references,
end pointers, counters, parser and latch backing are additional material.
Every received/transmitted bit, sealed reply, pending frame and actual
copy is backed as used. The root, dispatcher, adapter code, source and
work ownership/grant records are retained for their whole actual lifetime.
A two-bit constructor payload is not a total memory bound.

**Theorem 73.3 (finite continued-use account).** Suppose a completed
continuation contains $r$ addressed outer frames and $z$ unsupported
frames, with $k_P,k_S$ successful represented promotions/splits. Let
$J_{\rm all}$ be the sum of depths of all its addressed frames, and
$J_P,J_S$ the depth sums over its successful represented promotions/splits.
On this continuation the outer payloads are

$$
I_{\rm out}=2J_{\rm all}+4r+3z,\qquad
O_{\rm out}=5r+2(J_P+J_S)+3z.
$$

The real inner payloads and source changes are

$$
\begin{aligned}
I_{\rm in}&=4J_P+8k_P+2J_S+6k_S,\\
O_{\rm in}&=4J_P+10k_P+2J_S+7k_S,\\
\text{inner completion cycles}&=2k_P+k_S,\\
\text{added source vertices}&=3k_P+2k_S,\\
\text{source structural assignments}&=12k_P+8k_S.
\end{aligned}
$$

There are additionally $r+z$ outer completion cycles. At its final Ready
cut the represented leaf count is $L+k_S$, its beta count is $b+k_P$,
the source has $N+2b+3k_P+2k_S$ vertices, and its live word contains
$4(L+k_S)-2$ bits.

Proof. At represented depth $d$, a promotion uses two real calls at depth
$d$. Their total request/reply payload is $8d+18$, split as $4d+8$ input
and $4d+10$ output. They add one plus two vertices and four plus eight
structural assignments. A represented split uses one real call at depth
$d+1$, with $2d+6$ input and $2d+7$ output bits, two vertices and eight
assignments. Source-navigation descents and ascents for these two cases
are respectively $2d$ and $d+1$ in each direction. Outer successes have
request/reply total $4d+9$ in addition to that inner traffic. Outer
refusals have $2d+4$ input and five output bits and no inner call;
unsupported frames have three plus three. Summing proves every traffic
and work coordinate. A represented promotion raises beta count by one
and preserves leaf count; a represented split raises leaf count by one
and preserves beta count. The full-binary node formula then gives the
live-word count and, using the real vertex additions, the material count.
$\square$

For an explicit finite local implementation, parse each received frame
and scan the valid current preorder word to locate its logical target.
A stack of pending subtree slots permits skipping a nonselected subtree.
For a current $n_i$-node word and depth $d_i$, at most $O(n_i+d_i+1)$
constructor/address decisions suffice. On a success, copy to proposed
word backing while replacing the selected leaf symbol; this uses
$O(n_i+1)$ symbol writes. Retain old and proposed words until the real
macro completes; their constructor payloads are $2n_i+2n_{i+1}$ bits,
not their maximum alone. All stack/counter operations, their growing
widths, references, frame copies, reservations and sealed answers are
paid too. These are constructive operation counts for this layout, not
a unit-cost bound for arbitrary-width references or a polynomial bound
in the size of a succinct source description. Proper pending prefixes
pay their received bits and work even before a completion cycle exists.
Any retained outer transcript, old entry archive or exported view adds
its own actual material, construction, transmission and later use.

**Theorem 73.4 (clearing, second sweep and decode on the same specimen).**
In Definition 72.1's no-intervening-continuation experiment the second
sweep starts with

$$
n'=n+2b,\qquad
D'=D+2D_\beta+2b,\qquad D'_\beta=D_\beta+b
$$

logical-node and depth coordinates. It makes $n'$ split calls, exactly
$b$ successful, and adds $2b$ more material vertices. Its payloads are
$2D'+4n'$ input and $5n'+2D'_\beta$ output, with $n'$ complete cycles,
$D'$ descents and $D'$ ascents, and $8b$ source assignments. The physical
source finally has $N+4b$ vertices. The newly acquired word $J(t)$ has
$2n'$ content bits; keeping it while decoding a separate $t$ requires an
additional $2n$ output content bits, besides work and backing.

Proof. Each original beta at depth $d$ becomes one branch at depth $d$
and two leaves at depth $d+1$, with exactly one beta. Relative to the
original logical positions this adds two nodes, $2d+2$ to total depth,
and one to beta-depth sum. Summing gives the three coordinates. Apply
Theorem 73.2 to the actual second entry $J(t)$; its beta count is still
$b$ and its material size is $N+2b$. This proves all source/traffic
formulas on the actual successive run, rather than combining optima
from separate realizations.

The decoder can read its valid input preorder word once, using a backed
structural stack. Alpha emits alpha; a branch with immediate left beta
is the sentinel and consumes that beta and its right alpha, emitting
beta; any other branch emits branch and parses its children. The valid
range grammar proves these cases exhaustive and unambiguous. It uses
$O(n')$ constructor decisions and $2n$ output-content writes, in addition
to its actual stack, pointers, counters and operand widths. This is an
arithmetic/symbol operation account, not a total bit-complexity theorem.
$\square$

The clearing itself scans/overwrites or releases every accessible
entry-dependent occupied record specified in Definition 72.1, clears
its accessible metadata and pays every actual such operation. A receiver
that retained extra transcripts or exports pays to clear them too.
There is no negative material charge for inaccessible retained capacity.
At every cut total material counts the actual source's three reference
fields per vertex, every still allocated record/cell at its real width,
all code, cursor and allocator descriptors, actual root and grants,
I/O and pending latches, old/new/proposed/result copies and retained
backing simultaneously. Total work is the sum of their actual allocations,
field assignments, symbol/operand operations, communication, navigation,
clearing and retained-use operations, including old preparation. No
unspecified auxiliary source field is assumed; if a realization supplies
extra slots, their allocation and initialization are additional charges.
Finite conversion/export of §71's views also pays for every constructed
material address, terminal and labelled event/precedence record. These
charges prevent the payload formulas from being read as total-resource,
peak-memory, latency, energy or lifetime optima.

**Proposition 73.5 (a selected source-growth comparison only).** Let
$c_0=\beta$ and $c_{j+1}=\langle c_j,\alpha\rangle$. On entry $c_j$ the
split sweep adds two source vertices, while §54's normalization adds
$j$. Thus the former has a strictly smaller added-source coordinate for
$j>2$. This comparison does not give total or minimax dominance.

Proof. Induction gives $a=j,b=1$ on this reachable comb. Apply Theorem
73.2 and Theorem 54.2. The endpoints are $J(c_j)$ and $\nu(c_j)$, and
their continued tasks differ as specified above. Conversely, on the
reachable all-beta skeleton with $L$ leaves, normalization adds zero
vertices while this sweep adds $2L$. Real represented promotions also
need two inner calls. These same-run coordinates rule out a universal
source-growth comparison in the opposite direction and supply no total
ranking. The weighted randomized acquisition optimum of §§61–67 and
fixed-normalization bounds retain their own tasks, prices and endpoints.
$\square$

## 74. Supplier correspondence and applicability of recoverable acquisition

**Definition 74.1 (mathematical attribution).** The source-relative
`repo-derived` contribution is the conjunction of the actual split
sweep, its injective advanced source, the paid represented service at
that earned entrance, and the cleared one-reaccess experiment, with
§73's simultaneous account. Ordered syntax, generic encoding, traversal,
original source inverses, randomized minimax and information counting
are supplied mathematics rather than new abstract principles.

| Mathematical supplier | Exact application and boundary |
| --- | --- |
| [AA §§17,20–23](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md), AAII §§53–59 | Reachable birth typing, actual marker versus logical child, source causal/support/boundary inverses, complete guard lifecycle and structural assignments are used at the actual term $J(v)$. Normalization and its archived-entry service do not establish entry recovery after that archive is cleared. |
| AAII §§61–67, especially Theorems 62.3 and 66.2 | The public randomized acquisition already supplies entry-node traversal with complete guard replies, earned current use and application of the original inverse. Its GLOBAL/LOCAL mode-zero rule leaves forced $L$-ending betas unchanged; $J$ splits every entry beta, including those. No randomized weighted minimax or original-$Q_A$ inverse is reauthored here. |
| [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs); [NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs) | The former's private traversal, read-count and stationarity proofs use a nondestructive Native read unavailable here. The latter's private tree-view/child/walk helpers and `term_at_prim`, `readout_prim` act on supplied codes. These supply finite scheduling/navigation patterns, not this guard acquisition or new authority. |
| [SourceTreeEncoding](../../../D5/S0/History/Spacetime/SourceTreeEncoding.lean), [GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.scribe.cs) | Tagged finite-tree encodings and the existing substitution injection supply static syntax techniques. Their given-code maps and the substitution $\rho(\alpha)=\beta$ do not execute the present $J(\alpha)=\alpha$ acquisition or its real macros. Lemma 68.3 proves only the syntax obligations needed for this different actual construction. |
| Pinned mathlib [Algebra/Free.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Free.lean) | `FreeMagma.of`, `mul`, `liftAux` and `lift` supply the ordered binary syntax and structural fold. They supply no observation of an unknown source, binding, rights or recovery after an actual edit. |
| Bennett, [*Logical Reversibility of Computation*, IBM Journal of Research and Development 17, 525–532](https://doi.org/10.1147/rd.176.0525), [primary text](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html) | The classical distinction between information retention, history records and their clearing is background. Its reversible-machine construction is not invoked as a reversible LAB operation, free erasure, thermodynamic bound or source-restoration theorem. The present LAB edits remain irreversible and all clearing is paid. |
| [Native leaf-boundary acquisition II §§24–29](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md) | Public binary-mask/integer-age binding acquisition uses a complete raw roster, field Reset/Add/Read and fresh-zero inheritance. Its unknown raw maps and full field continuation are stronger and different inputs/outputs; they supply neither these guard-only macros nor a new raw binding here. |
| [Unknown-field startup §§27–33](RECURSIVE_RELATIONAL_OBSERVATION_UNKNOWN_FIELD_NATIVE_STARTUP.md) | The public signed source-provenance producer constructs its rational path/Jacobi observation law under its stated positivity and authentication hypotheses. No map realizing that source by LAB guards is supplied or inferred. |

**Definition 74.2 (distinct source domains).** The conditional all-mode
spectral count in [Native attractive boundary response §18](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md),
the maximal zero-mode source-germ theorem in [Atomic boundary continuation
appendix §108](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md),
and the outside-band private-randomized clock bounds in [Quadratic clock
§8](FIB_UNCALIBRATED_QUADRATIC_CLOCK_PRIVATE_RANDOMIZATION.md) concern,
respectively, a continuum boundary-response operator, critical differential
zero modes, and complete exact-real report worlds. Their hypotheses and
observations do not install addressed LAB guards, the encoding $J$ or
its macro service. The present supplier-relative attribution is not a worldwide
originality claim.

The chosen construction adds no source generator. A split alone suffices
for its acquisition. Its full represented continuation uses both original
generators: from the physical alpha entry a controller using only splits
cannot reach the required promotion endpoint $J(\beta)$, since every
split refuses; from a physical beta entry promotions alone cannot create
its required encoded branch. These facts justify the generator uses in
this construction, without proving a universal minimal alphabet. One
live word, actual bindings and a finite backed controller suffice at
Ready; old/proposed words and protocol state coexist during transactions.
The canonical two-bit word is an explicit sufficient layout, not a
minimal information code or a lower bound on total retained material.

The four-view conclusion is conditional on original-root oriented LAB
birth typing and exact returned-image membership, authentic retained
access, complete serialization and sufficient actual finite backing.
It concerns causal source time rather than total physical history, and
current live Memory rather than the full private process state. Data
recovery cannot certify the attachment premises or create missing rights.
The paid clearing experiment requires its stated inaccessible-side-channel
and clearing-authority conditions. Concurrent raw clients, crash recovery,
noise, revocation, observable exhaustion and arbitrary busy cuts are
outside this installation.

No stationary entry retrieval, raw-original-interface equivalence,
arbitrary erased-history recovery, fixed-endpoint optimum, total resource
dominance, native LAB-to-rational-path or quantum realization, or universal
minimal generator theorem follows. Existing fixed-$G_{\rm gc}$,
original-$Q$, parked-consumer, unchanged-initialization, terminal and
final-no-Ready statements retain their original scopes. A common actual
realization joining the distinct LAB, path/field and quantum models, with
the full programme's observations and resource obligations, remains a
separate missing bridge. The scoped actual acquisition and represented
continued use proved here do not assert that broader completion.

## 追加锚（本行以下为增补区）

