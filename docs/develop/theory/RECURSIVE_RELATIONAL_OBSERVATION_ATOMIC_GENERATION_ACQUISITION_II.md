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
