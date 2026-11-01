# Atomic generation and acquisition IV: sharp immutable complete-word memory

## 1. Native histories and the complete-word observation

**Definition 1.1 (the common native source).** AA denotes
[Atomic generation and acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md),
and AAII denotes its
[second volume](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md).
Use exactly AA Definitions 17.1–17.3's known-alpha LAB:

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle,\qquad
P_p:\alpha\longmapsto\beta,\qquad
S_p:\beta\longmapsto\langle\beta,\alpha\rangle.
\tag{IV.1}
$$

The split's beta child is on the left. The logical root address is
$\varepsilon$, and other logical addresses are words in $L,R$. An address
is born beta precisely when it ends in $L$; the root and right-born
addresses are born alpha. Let $\mathcal D$ be the reachable finite terms,
equivalently those with no alpha leaf at an $L$-ending address. Let
$\mathcal H(t)$ be the **complete** fibre of all finite legal successful
addressed-event histories from the known alpha to $t$, including every
legal interleaving. Write

$$
F(t)=|\mathcal H(t)|,\qquad
N(t)=a(t)+2c(t)-1,\qquad
g(t)=\lfloor\log_2 F(t)\rfloor,
\tag{IV.2}
$$

where $a,c$ count logical alpha and beta leaves. Here $N(t)$ is the length
of every member of $\mathcal H(t)$, by AA Proposition 22.1. Successful
generation chronology excludes queries, refusals, ingress, maintenance,
printing, waiting and return. In particular $\mathcal H(\alpha)$ is the
singleton empty history and $F(\alpha)=1$.

Use AAII Definition 99.1's full **labelled** predecessor set
$\operatorname{Pred}(t)$. A beta leaf at a root or right-born address $p$
can be replaced by alpha, giving the incoming edge labelled $P_p$.
An exact subtree $\langle\beta,\alpha\rangle$ at any logical address $p$
can be replaced by beta, giving the edge labelled $S_p$. These are all
incoming edges. An $L$-born beta leaf is not a promotion predecessor.
Distinct edge labels remain distinct even when their unlabelled data
would coincide. For noninitial $t$, AAII Proposition 99.2 supplies the
actual last-event partition

$$
\mathcal H(t)=\bigsqcup_{e:u\to t}
 \{he:h\in\mathcal H(u)\},\qquad
F(t)=\sum_{e:u\to t}F(u),\qquad N(u)=N(t)-1.
\tag{IV.3}
$$

Every predecessor is reachable and its displayed forward edit is enabled.
AA Theorems 17.2 and 19.2 supply finiteness, positivity, the labelled
causal-order interpretation and the equivalent product of local shuffle
counts. These are source suppliers, not additional claims of this volume.

**Definition 1.2 (observable whole words and immutable data).** A record
value is a finite binary word **with its current end observable**, including
$\varepsilon$. Write $q\preceq x$ for literal, non-strict word prefix.
Two words may be prefix-related within one source fibre. A decoder reads
the entire present word through its end; encountering an earlier codeword
prefix does not end decoding. There is no instantaneous or prefix-free
code requirement. A successful extension must preserve all old data bits
in order: $J(h)\preceq J(he)$. The end can move when a suffix is appended.
An immutable old delimiter, fixed-width field or immutable old tail link
would impose a different contract.

The selected payload charge is $|J(h)|$. Observable termination is part of
the word alphabet, not an uncounted independent history field. Its actual
header, links, reference widths, end movement and observation work are
separately paid as in §§5 and 7. No source-dependent event boundary,
per-event counter, persistent codebook, request archive or extra serial
metadata accompanies the word. The conditioning is the current source and
the fixed binding/rights context specified in Assumption 5.1. A separately
observable varying history channel would change that conditioning.

**Convention 1.3 (one deterministic convention at every grade).** Order
an event by the tuple $(\mathrm{kind},|p|,p)$, with $P<S$ and $L<R$.
Order complete histories first by event count, then lexicographically by
these event tuples. To allocate labelled tokens with lower-bound words,
process tokens by decreasing lower-bound length; break ties by their
complete history. At an occupied binary node, choose child $0$ if its
subtree load is strictly below its quota, and otherwise choose child $1$.
These rules are fixed for every source, without an endpoint horizon.
They also govern every named codeword below.

**Definition 1.4 (prefix quotas).** For an integer $F\ge1$ and $d\ge0$ put

$$
c_d(F)=\left\lfloor\frac{F}{2^d}\right\rfloor.
\tag{IV.4}
$$

For a finite set $C$ of distinct words write
$\lambda_C(q)=|\{x\in C:q\preceq x\}|$. For the codebook of a source,
write $\lambda_t(q)=|\{h\in\mathcal H(t):q\preceq J(h)\}|$.
Quotas refer to subtrees of the tree of **terminated words**, whose nodes
as well as descendants may be occupied. They do not refer to disjoint
infinite cylinders of a prefix-free code.

## 2. Simultaneous sharp allocation on all native fibres

**Theorem 2.1 (sharp coherent native complete-word recorder).** There is
one deterministic computable map $J$ on all finite legal LAB histories,
independent of any future horizon, such that for every reachable source
$t$, every $h,h'\in\mathcal H(t)$, every legal next event $e$, and every
finite binary word $q$,

$$
\begin{aligned}
J(h)=J(h')&\Longrightarrow h=h',\\
J(h)&\preceq J(he),\\
\lambda_t(q)&\le c_{|q|}(F(t)),\\
\max_{h\in\mathcal H(t)}|J(h)|&=g(t).
\end{aligned}
\tag{IV.5}
$$

Prefix preservation consequently holds along every finite legal extension.
At **each** source the displayed maximum is minimal among all full-fibre
injections into complete observable binary words, even without a coherence
requirement. The same single recorder attains all these minima while
preserving literal history prefixes.

Proof. We use finite prefix-subtree allocation inside induction on the
native grade $N$. The allocation argument is included to specify both the
chosen codebooks and the strict-ancestor obligation.

For $g=\lfloor\log_2 F\rfloor$, integer division gives

$$
\begin{gathered}
c_0(F)=F,\qquad c_g(F)=1,\qquad c_{g+1}(F)=0,\\
c_d(F)\in\{2c_{d+1}(F),\,2c_{d+1}(F)+1\},\\
\sum_i c_d(F_i)\le c_d\!\left(\sum_iF_i\right).
\end{gathered}
\tag{IV.6}
$$

For the last inequality write $F_i=2^d k_i+r_i$ with
$0\le r_i<2^d$ and sum. The preceding identity implies
$c_d(F)\le1+2c_{d+1}(F)$.

First consider distinct already assigned words $C$ satisfying all quotas
for this $F$. If $\lambda_C(q)<c_{|q|}(F)$, a new word extending $q$ can
be inserted while preserving all quotas at or below $q$. If $q$ is not
occupied, insert $q$ itself. If $q\in C$, put $d=|q|$. Its two child loads
satisfy

$$
\lambda_C(q0)+\lambda_C(q1)=\lambda_C(q)-1
 <c_d(F)-1\le2c_{d+1}(F).
\tag{IV.7}
$$

At least one child therefore has strict slack. Descend into the child
chosen by Convention 1.3 and repeat. Every visited node has strict slack.
No such node has depth greater than $g$, since its quota would be zero.
At depth $g$ a slack node cannot be occupied: occupancy would give load
at least one, equal to its quota. Hence descent reaches a free node $x$
after finitely many steps. Inserting $x$ raises the loads exactly along
its ancestor chain, where strict slack has been established below the
starting $q$. All other loads remain unchanged. Strict ancestors above
that starting node still need their own slack; this local argument alone
does not supply it.

Now take exactly $F$ labelled tokens with lower-bound words $b_i$, allowing
repeated lower bounds, and suppose their multiplicity demand satisfies

$$
D(q):=|\{i:q\preceq b_i\}|\le c_{|q|}(F)
\quad\hbox{for every }q.
\tag{IV.8}
$$

Process tokens in Convention 1.3's decreasing lower-bound-length order.
Suppose the current token is $i$ and earlier tokens $j$ have been assigned
distinct words $x_j\succeq b_j$ obeying all quotas. For **every** ancestor
$q\preceq b_i$, if $q\preceq x_j$, then

$$
|b_j|\ge |b_i|\ge |q|,\qquad b_j\preceq x_j
\quad\Longrightarrow\quad q\preceq b_j.
$$

The current token itself contributes to $D(q)$, so

$$
\lambda_C(q)\le|\{\hbox{earlier }j:q\preceq b_j\}|
\le D(q)-1<c_{|q|}(F).
\tag{IV.9}
$$

This supplies strict slack at $b_i$ **and every strict ancestor** of
$b_i$. Apply the preceding descent starting at $b_i$. The new assignment
$x_i$ extends its own lower bound, is distinct from earlier assignments,
and preserves every quota: (IV.9) covers the ancestors above $b_i$, the
descent covers the path below it, and other nodes are unaffected. Repeat
for all tokens. The length comparison here is between lower bounds,
not between the lengths of already assigned words.

Apply this construction to the actual native predecessor partition.
At alpha assign $J(\varepsilon)=\varepsilon$; its singleton codebook
satisfies the quotas for $F=1$. Having defined all lower grades, fix a
noninitial $t$. For every labelled incoming edge $e:u\to t$ and every
$h\in\mathcal H(u)$, form the token labelled $he$ with lower bound
$b_{he}=J(h)$. By (IV.3) these are exactly all $F(t)$ distinct histories
at $t$. For $d=|q|$, the already proved predecessor quotas give

$$
D_t(q)=\sum_{e:u\to t}\lambda_u(q)
 \le\sum_{e:u\to t}\left\lfloor\frac{F(u)}{2^d}\right\rfloor
 \le\left\lfloor\frac{F(t)}{2^d}\right\rfloor.
\tag{IV.10}
$$

Multiplicity is over labelled incoming edges; no predecessor fibre or
history is discarded. Allocate these tokens by the preceding argument
and define $J(he)$ to be their assigned words. Distinctness gives the
whole-fibre injection, the lower-bound condition gives the immediate
prefix law, and all quotas are preserved. Every predecessor grade is
strictly smaller, so induction defines one family on all finite histories.
Its choices at $t$ use only predecessor codebooks and the fixed convention;
no future source or maximum grade is consulted. Iterating the immediate
prefix law proves preservation along every legal continuation.

The quota at depth $g(t)+1$ forbids any longer codeword, proving the
upper bound on maximum length. For $g(t)\ge1$, the number of complete
binary words of length at most $g(t)-1$ is $2^{g(t)}-1<F(t)$. Thus no
injection of the full fibre can have a smaller maximum. If $g(t)=0$,
then $F(t)=1$ and the maximum is zero. More generally, maximum $L$ allows
exactly $1+2+\cdots+2^L=2^{L+1}-1$ complete word values; this is the
standard complete-word count, already used in EndpointFiniteWordRecovery
Corollary 90.3. Its application here proves the static lower bound
$\lfloor\log_2 F(t)\rfloor$. The construction attains it simultaneously
at every source. The finite algorithm and its inverse are detailed in
Theorem 3.1. $\square$

**Corollary 2.2 (the ceiling guarantee is retained).** The same recorder
satisfies $|J(h)|\le\lceil\log_2 F(t)\rceil$ for every
$h\in\mathcal H(t)$, with the complete domain and literal prefix law
unchanged. This follows directly from (IV.5). It neither rewrites nor
weakens the distinct fixed-width obstruction of AAII §100.

## 3. Effective native construction and exact whole-word recovery

**Theorem 3.1 (finite source-derived computation and inverse).** A fixed
finite program, given a finite reachable source term $t$, computes the
entire finite table $(h,J(h))_{h\in\mathcal H(t)}$ of Theorem 2.1.
Given $(t,j)$ with the entire current end of $j$ observable, it decides
whether $j$ belongs to that table and, on the table's image, returns the
unique complete addressed history $h$. For an actual enabled edge
$e:t\to u$ and an on-image $(t,J(h))$, it computes the exact suffix $s$
satisfying $J(he)=J(h)s$. No persistent advice, future horizon or separately
remembered event boundaries are needed.

Proof. Parse the finite term and enumerate precisely Definition 1.1's
incoming labelled edges. A predecessor replacement is a syntactic
calculation on work data, not an edit of the live source. Its grade
is one smaller. Recursive enumeration therefore terminates at alpha;
finite branching and finite depth make the entire recursion finite.
Appending each full last label to each enumerated predecessor history
gives exactly (IV.3), including all shuffles. Counts can be obtained
from these finite lists, or from AA Theorem 19.2's source-derived product.
An independent source count does not select a smaller history domain.

Recursively compute the predecessor tables and the lower bounds in
(IV.10). Sort by Convention 1.3. Loads, integer divisions, finite sets,
word comparisons and descent through at most $g(t)$ bits are finite
operations. The argument of Theorem 2.1 guarantees a choice for every
token. This computes the unique table specified by that convention.
Shared recursion may be recomputed instead of memoized; any temporary
memoization is ordinary finite work backing, cleared before a returned
service cut. Neither choice places a source-dependent table in the
fixed program or retained history record.

Compare the **entire** observed $j$, including its end, with every computed
entry. Injection gives at most one match, and on-image membership gives
one. Return its full literal kind/address sequence. Equality of complete
words handles empty records and prefix-related entries: for example,
reading $0$ does not match an entry $\varepsilon$. The source-derived
$N(t)$ is also the exact length of the recovered event list. Rejection
of off-image data is a mathematical image test; it is not an additional
reply case of the original maintained service.

For encoding an enabled edge, use the current table to recover $h$,
form the prospective term $u$ in scratch by the actual beta-left rule,
and compute its table. Lookup of the label $he$ gives $J(he)$. Theorem
2.1 proves that removing its initial $|J(h)|$ bits leaves exactly a suffix
$s$ and never requires an old data-bit change. No prospective source is
queried as if it already existed. All histories, tables, integer counts,
syntax copies and suffix calculations are charged finite scratch, not
persistent advice. There is no efficiency bound in this conclusion.
$\square$

## 4. The original consumer distinguishes terminated internal nodes

**Proposition 4.1 (one declared codeword pair and its real consumption).**
Let

$$
\begin{aligned}
t_*&=\langle\langle\beta,\alpha\rangle,\beta\rangle,\\
h_A&=P_\varepsilon S_\varepsilon P_RS_L,\\
h_B&=P_\varepsilon S_\varepsilon S_LP_R.
\end{aligned}
\tag{IV.11}
$$

These are exactly the two histories at $t_*$. Convention 1.3 gives
$J(h_A)=\varepsilon$ and $J(h_B)=0$. On this same current source the
original FetchGrowth$(3)$ returns $P_R$ and $S_L$, respectively. Original
current-source Next$(3)$ then executes $S_R$ and $S_{LL}$, respectively,
and returns the corresponding old/new pairs and different real successors.
Thus observable word length supplies a distinction actually consumed by
the original service.

Proof. Root promotion and root split are forced. The remaining two events
$P_R$ and $S_L$ are incomparable and enabled in either order, giving
precisely the two histories by AA Theorem 17.2. Each of the two immediate
predecessor endpoints has a singleton history fibre, so its lower-bound
word is empty. At $t_*$, $F=2$, $c_0=2$ and $c_1=1$. History $h_A$ comes
first because $P<S$; allocation first occupies $\varepsilon$ and then,
from that occupied node, chooses the free slack child $0$. FetchGrowth's
third full event is as displayed. The historical address $R$ is a current
beta leaf, whereas historical address $L$ is a current branch whose left
logical child $LL$ is beta. Definition 20.4 of AA therefore gives exactly
the two split operations. The actual source binding and rights are those
of §5, not manufactured by the two binary descriptions. $\square$

**Proposition 4.2 (compatibility with the exact-width obstruction).**
Theorem 2.1 does not satisfy the exact-width premise of AAII Theorem
100.3 and does not contradict its native obstruction. On its three
witness fibres of sizes $35,35,126$, the present maximum lengths are
$5,5,6$, while AAII §100's fixed widths are $6,6,7$.

Proof. AAII §100 requires every word at a source to have its stipulated
common width. Here occupied internal nodes are valid terminated values,
and some codewords can be empty even in a nonsingleton fibre. In a
one-additional-bit budget, a terminated prefix $x$ has three possible
terminated extensions $x,x0,x1$; an exact one-bit-longer width has only
$x0,x1$. The fixed-width cylinder-capacity argument therefore has a
different counting premise. The local three-value observation is not
itself an existence proof for simultaneous native demands; (IV.6)–(IV.10)
provide that proof on the full domain. In particular no padding to a
common source width has been used: such padding need not preserve the
literal history-prefix law. AAII §100's conclusion on exact widths
retains its original scope. $\square$

## 5. Conditional finite driver and all seven original requests

**Assumption 5.1 (acquired bindings, progress and resource context).**
Use exactly AA Assumption 20.1 and AAII Definitions 75.1 and 83.1's
finite-service context. There is an actually allocated known-alpha root,
current exclusive source and auxiliary record rights, genuine bindings
returned by allocation, licensed field reads/writes and reference tests,
backed finite work, finite supplied bit-input/output progress and the
supplied local acknowledgement. Each asserted finite completion has
sufficient actual finite backing. There is no concurrent writer,
revocation, crash, interrupt, reset, source deletion or observable
quota/exhaustion branch. Missing rights or the wrong phase disable a
primitive; they do not produce new refusal answers.

The driver, source-independent program, root binding and input/output
connections are supplied before an arbitrary finite schedule. The source
has its original parent, left, right and auxiliary-reference fields.
As permitted by AA Proposition 22.2's alternative-record principle, replace
the routing tapes by the word record below while retaining the whole
original task. Current source traversal uses only the already licensed
field operations. No stationary Native read port, arbitrary reference
cast, automatic grant, free traversal, erased old archive or unknown
late-history initialization is added.

Task observations are exactly AA Definition 21.1's semantic service
observations, with the word replacing tapes. Raw fresh-name spellings,
allocator/control chronology, unexposed capacity, cleared scratch and
primitive duration are excluded. Any additional observable varying serial
information must instead be included as side information in a different
conditioning. This is an observation restriction, not a consequence of
paying for that information.

**Definition 5.2 (returned word layout and invariant).** Install one fixed
root-bound owned header with head and tail fields; at alpha both are null.
For $\ell=|J(h)|>0$, they bind a chain of exactly $\ell$ owned bit/next
cells carrying $J(h)$ in order; the last next field is null. For
$\ell=0$ there is no data cell. All other source auxiliary-reference
fields are null. The header and every reference/link field are charged
material, separate from $\ell$. Only data-bit values are immutable;
head, tail and next links may change to append and move the observable
end. A zero-bit extension creates no per-event marker or event header.

The returned invariant is

$$
\mathsf{Ready}(h)=
\bigl(t(h),\ \text{bound chain with complete contents }J(h),\
       \text{current source/record/input/output rights}\bigr),
\tag{IV.12}
$$

where $h$ is the actual successful-generation word from that alpha.
The cursor is at the same root. Acquired input, pending result, suffix,
reservation, occupied decoder/work contents and output are empty, with
no unfinished edit or append. Retained cleared capacity is paid but is
not a second semantic history observation. The header/chain shape is
fixed by the complete word up to unexposed fresh-name spelling, rather
than selecting an independent history value. Ready is a completed return
cut, not a name for an intermediate source/word discrepancy.

**Theorem 5.3 (completion-conditional unchanged full service).** Under
Assumption 5.1 there is one fixed finite driver, initialized as in
Definition 5.2, maintaining (IV.12) for every finite adaptive sequence
of complete original requests with sufficient backing and supplied
progress. Each complete request has its exact original full reply,
local acknowledgement, return to the same root and original semantic
successor. All seven kinds are included: Tag, addressed $P/S$,
HasPromotion, HasSplit, FetchGrowth and internally continued Next.
The unused tag returns BadFrame. Every finite legal native growth word
can occur. A proper incomplete frame retains its actual acquired prefix
and returns under a supplied finite completion. Old record data bits
are preserved through every successful extension.

Proof. The finite driver uses the original request and reply grammar of
AA Definition 20.2. Each request tag is three bits. Tag, $P$, $S$,
HasPromotion and HasSplit take $A(p)=1^{|p|}0p$; FetchGrowth and Next take
$U(k)=1^k0$. Reply tags are the original eight disjoint three-bit tags:
Tag carries its two-bit constructor/absence result, Boolean one bit,
Refusal its two-bit reason, Growth and Recall each a kind bit and full
$A(p)$, Next two such kind/address pairs, and OutOfRange and BadFrame
no payload. We specify the phases and their preserved data.

Receive copies each occupied input-latch bit into backed request storage
before releasing the latch or admitting the next bit. Actual length/index
marks, remaining-address marks, tag and parser subphase retain precisely
the acquired frame prefix. A proper prefix waits; it neither reads an
unsupplied bit nor seals an answer. The prefix-free complete-frame
grammar supplies a unique finite completed request. An acquired address
is navigated on the actual current source, testing logical arity before
each child; a unary beta marker is not a logical child. The retained
root, current operand and remaining path are genuine bindings.

For an enabled $P/S$, Guard has acquired its actual kind, target and
full logical address. With already backed workspace, traverse the
licensed source and apply Theorem 3.1 to decode $h$ and compute the
prospective term $u$, its table and the exact suffix $s$ for $he$.
Workspace is supplied before each finite calculation uses it. Reserve
the exact $|s|$ fresh cells, the original finite source template, and
sufficient pending/reply backing **before** the actual source edit.
Serialization ensures that $u$ is the result of that guarded edit.
Retain the event identity, actual target, suffix, remaining suffix count,
append cursor, references and subphase throughout the transaction.

Execute the original material source template: $P$ attaches one new
terminal left marker; $S$ reuses the old unary marker as the new left
logical beta root, attaches that child's new left marker, and attaches
a new right alpha root to the old target. Initialize the genuine parent
and other fields. These are precisely the beta-left edits (IV.1), without
source deletion. The global header remains bound to the retained root;
new source auxiliary fields are null. No local routing tape is needed
for this alternative recorder.

Maintain appends only $s$. For each bit, initialize a reserved cell's
bit and null next field, link it from the old tail or empty head, and
then advance the header tail. Explicit pending references and subphases
record a linked-but-not-yet-advanced cell and the remaining suffix.
No input or query is admitted while reservation, editing, append or
pending maintenance is incomplete. Every loop has a finite backed
remaining list or count. When $s$ is empty, maintenance makes no data
cell or event marker. Before answering, the actual source is $u$ and
the complete chain is $J(h)s=J(he)$. Earlier data bits have not changed.
A busy cut can precede this equality; (IV.12) is not asserted there.

For the nongrowth cases, Tag returns the actual logical alpha, beta,
branch or absence result. HasPromotion is true exactly at present
root/right-born addresses whose current subtree is not alpha;
HasSplit is true exactly at branches. Both return false absent.
Addressed $P/S$ at an absent address, branch or wrong-type leaf returns
exactly its original Refusal reason, without changing source or record.
These cases use current source predicates, not a prospective endpoint.
Queries, refusals and BadFrame append no bits and add no generation
event. The unassigned three-bit request tag produces exactly BadFrame.

For FetchGrowth, acquire $N(t)$ from the actual finite source.
Indices $k=0$ and $k>N(t)$ give OutOfRange. For
$1\le k\le N(t)$, Theorem 3.1 recovers the full word and returns its
literal $k$th kind and entire logical address, including at $k=N(t)$.
All enumeration, comparisons and index marks have finite backed storage.
The complete current end, not a presumed chunk boundary, is read.

Next invokes this same retained decoder **internally**, preserving its
index, old pair, continuation and references. OutOfRange gives the
original no-growth result. Otherwise let the acquired pair be $(e,p)$.
The historical logical position $p$ persists on the same current source:
a split preserves its root position and no source position is deleted.
Navigate from the retained root to $p$, then follow actual logical left
children while the current subtree is a branch. Finite descent reaches
a current leaf $q$. Its current tag selects $P_q$ for alpha or $S_q$
for beta. Execute that genuine enabled edit using the preceding suffix
transaction for this actual new event. Seal **one** Next reply containing
the acquired old pair and the actual new kind/address pair. There is
no extra external Fetch reply, intermediate outer return or extra ACK.
This is current-source continuation, not replay on a reconstructed old tree.

Every complete outer request constructs and seals its entire original
reply in backing before Print traverses it. Supplied finite output
progress emits all its bits followed by End. The supplied local ACK
then enables Return to the same retained root. Clear occupied request,
index, traversal, decoder-table, suffix, pending-continuation and output
contents, discharge reservations, and only then admit Ready. Cleanup
is finite on the actually occupied finite work; allocated cleared
capacity may remain and is charged. No cleared scratch is used as advice
for a later request. All cases therefore restore (IV.12).

At alpha the history and word are empty, the source is the known alpha,
and initialization satisfies (IV.12). Induction on received bits proves
the partial-ingress assertion; induction on completed adaptive requests
proves the exact replies, invariants and semantic successors. Successful
edits append the actual event to $h$; other requests leave it unchanged.
Earlier FetchGrowth answers persist because decoding returns $h$ or its
actual extension. Supplying the original addressed $P/S$ frames of any
finite legal word makes each guard accept by AA Theorem 17.2. The fixed
driver thus admits the entire native domain, not a chosen set of schedules.
Every computation and phase above has a finite description and uses only
finite loops, charged primitive operations and backed data. Completion
is conditional on the stated supplies, not an assertion of an infinite
run on one finite device. $\square$

## 6. Four expressions on their actual returned image

**Definition 6.1 (the common-context views).** Fix one Assumption 5.1
installation, its actual root binding, current rights and returned domain.
Let $C(t)$, source support $S_0$ and terminal antichain $B_0$ be AA
Definition 17.3's material tree and views: alpha is terminal, beta has
one terminal left marker, and a branch has its two ordered logical
subtrees. Auxiliary record edges are excluded from this source geometry.
At a returned cut define

$$
\mathsf{Space}=(S_0,J(h)),\qquad
\mathsf{Boundary}=(B_0,J(h)),\qquad
\mathsf{Time}=h,\qquad
\mathsf{Memory}=M_J.
\tag{IV.13}
$$

Each word component includes its observable end. $M_J$ selects the actual
retained source, root-bound readable word chain, callable fixed driver
and present authority. It is not a table of hypothetical answers or the
whole controller's busy state. All four views have the same fixed live
binding/rights context. Equality of semantic contents disregards raw
fresh-name spellings and unobserved cleared capacity, as in AA §21;
it does not identify unrelated roots or different authorities.

**Theorem 6.2 (faithful returned-image inverses and operation agreement).**
On the actual image (IV.13), the four views recover the same semantic
state, all inverse routes agree, and they commute with every original
$Q_g$ request's full reply and returned successor under the same source
and rights. They have exactly the original full-task kernel there.
Bare $S_0$ and $B_0$ do not in general recover serial successful time.
A semantic inverse supplies no absent live binding, allocation or right.

Proof. Prefix closure of the terminal antichain gives source support,
and maximal elements of the support give the terminal antichain.
Arity parsing, including every unary beta marker, recovers $t$ from
either. The supplemented complete word and Theorem 3.1 then give the
unique $h$. Traversal of the actual backing selected by $M_J$ gives the
same $t,J(h)$ and hence that same history.

Conversely replay $h$ from the known alpha using the actual rule (IV.1)
as a finite semantic calculation. This recovers $t$, its material support
and terminal antichain. The fixed allocation of Theorem 2.1 recovers its
unique complete $J(h)$. With the already fixed live context and the
maintained record of Theorem 5.3, these are the contents selected by
$M_J$. This last route identifies the corresponding acquired callable
state; it does not create one from a history string. Physical conversion,
new object creation, references and grants require their separately
supplied operations and charges. The reconstruction is asserted on the
actual maintained image with that context, not on arbitrary unbound
numbers claimed to be memories.

Every route therefore factors through the same pair $(t,h)$, so inverse
and triangle identities hold on these images. Theorem 5.3 says that every
request uses exactly this current $t,h$ for its original reply and
successor; a successful event gives $(t',he)$ and a query or refusal
leaves $(t,h)$ unchanged. Its internal Next uses the same decoded pair,
current navigation and actual new event. Induction on finite request
sequences gives operation agreement and commuting returned-state routes,
including complete Next replies and corresponding source changes.

For faithfulness, distinct finite logical terms have different Tag
answers at a first different constructor/address. At the same term,
distinct full histories have the same source-derived length $N(t)$ and
differ in some full indexed event; FetchGrowth at that index separates
them. Equal $(t,h)$ gives equal replies and related successors by the
service theorem. Thus the full-task kernel is precisely equality of
these semantic states in the fixed context. Proposition 4.1 has the
same bare material tree, support and terminals on its two histories,
but different indexed recall and actual Next successors. It proves the
bare-geometry nonrecovery assertion. Successful-generation order is not
physical duration or the chronology of ingress, maintenance and outputs.
No busy-cut inverse follows from these returned-image identities.
$\square$

## 7. Information and resource boundaries

**Definition 7.1 (separate coordinates on the same finite execution).**
At a returned cut the selected retained payload is exactly
$\ell=|J(h)|$, with source-conditioned maximum $g(t)$. A linked
realization as in Definition 5.2 also pays the fixed root-bound header,
$\ell$ bit/next cells, all reference widths and the actual bindings.
The word's end contributes distinguishability under Definition 1.2;
observing and moving that end is not free physical work. The stream may
retain its old tail data bit while modifying that cell's next reference
and the header tail. Those are separately counted writes.

The same execution pays for source vertices and parent/child/auxiliary
fields; licensed source traversals, genuine guards and edits; reservation,
cell initialization, link/end/header maintenance and authority operations;
whole-source syntax copies, full predecessor/history enumeration, sorting,
integer counts, loads, codebooks, complete-word comparison and replay;
old stream and reserved suffix coexisting with occupied work; acquired
input, parser marks, internal Next's old/new operands and continuation;
full reply backing, Print, End, local ACK, root Return and clearing;
and retained cleared capacity. A singly linked scan pays each traversal.
Backing is supplied before its contents are used. These additional
coordinates are not bounded or minimized by the payload formula (IV.5).

At returned cuts every varying serial distinction in the permitted
supplement is in the complete word and its end. Independently visible
allocator identities, retained archives, capacities or controller
chronology would enlarge the observation and invalidate a binary-word-only
lower-bound comparison unless included in the conditioning. Merely
charging for such a channel does not erase its information.

**Proposition 7.2 (scope of the attained minimum).** Theorem 2.1's optimum
is the per-source worst-case **data payload** for the complete-word
contract, simultaneously attainable under literal data-prefix preservation.
It is not a pointwise shortest-codeword assertion or a total, physical,
peak-material, work, runtime, energy or Pareto optimum. Its conditional
driver neither acquires an unknown erased-history prefix nor extends
its inverse to all busy cuts, interrupted writes or an actual infinite
execution on a fixed finite device.

Proof. The lower bound counts only complete word values at one fixed
source. It contains no lower bounds for the additional coordinates of
Definition 7.1, and different histories can have different lengths at
that source. Prefix coherence is proved for finite extensions, while
Theorem 5.3 quantifies finite schedules with their sufficient actual
resources. Neither statement supplies a fixed capacity for all grades.
The source/word invariant is initialized at the actual known alpha and
maintained before returned cuts; it asserts neither recovery after
unsupplied erasure nor equality at unfinished maintenance cuts. The
current-source live-context premises remain necessary to call the
original service. Existing reset/tape experiments, terminal obligations,
original-$Q$ and unchanged-initialization results keep their own domains.
A cross-model physical common realization or universal minimal relation
generator is not a consequence of this finite LAB result. $\square$

## 8. Mathematical suppliers and attribution limits

**Correspondence 8.1 (existing results subtracted from the increment).**
The source references in this volume concern the stated mathematical
interfaces at revision
[`820ce45a8d16231a91e4c688c769bc0ebd3e690f`](https://github.com/the-omega-institute/trureturing/tree/820ce45a8d16231a91e4c688c769bc0ebd3e690f).
The following are reused supplies, not new enumeration, geometry or
coding theorems.

| Supplier | Exact role and retained boundary |
| --- | --- |
| AA §§17–22; AAII §§60 and 99.1–99.2 | Actual beta-left source, all finite histories, material support/terminal parsing, source-derived event count, full labelled last-event partition, original request/refusal/Next semantics and the current access/return hypotheses. The present proof uses every full fibre, not a restricted execution family. |
| AAII §§75–83, especially Theorem 81.1 | Existing installed rewriting global rank with $G(t)=\lceil\log_2 F(t)\rceil$ data bits and complete service. Its reranking and rewriting contract is distinct; its construction and conditional optimum are not new here. |
| AAII §§93–98 | Existing immutable ordinal journal and original service, with its own source-conditioned payload. Retaining this alternative does not establish total-resource dominance by either recorder. |
| AAII §99 | Existing weighted predecessor journal, exact sum of rounded predecessor-ratio lengths and full service. Its tail-read prefix-free property and rounding families are constructor-specific. The complete-word alphabet here drops that prefix-free constraint; it does not refute its conditional Kraft converse. |
| AAII §100 | Native impossibility for exact source-dependent widths under literal prefix preservation. Proposition 4.2 keeps this obstruction and separates the observable-end variable-word contract. |
| [EndpointFiniteWordRecovery, Corollary 90.3](RECURSIVE_RELATIONAL_OBSERVATION_ENDPOINT_FINITE_WORD_RECOVERY.md) | The mature count $2^{B+1}-1$ for complete words of length at most $B$ already appears there. Its source-specific geometric lower bound is not imported into LAB; only the elementary word-alphabet count is used in Theorem 2.1. |
| [SourceTreeEncoding.source_code_equiv](../../../D5/S0/History/Spacetime/SourceTreeEncoding.lean), [EnabledPathSwapConnectivity.result](../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean) and their owning Blueprint narratives | Existing static syntax equivalence and finite lower-set execution/linear-extension mathematics under their declared types. AA supplies the actual native/material correspondence. Neither generic result supplies changing codebook coherence, live authority or the present driver. |
| [ImmutableExtension](../../../D5/S0/Computability/Coding/ImmutableExtension.lean) and [LengthProfileSeparation](../../../D5/S0/Computability/Coding/LengthProfileSeparation.lean) | Existing frozen prefix-free code extension requires new words to be prefix-incomparable with old ones. The current requirement instead extends each history's own lower-bound word and permits occupied internal nodes. That API is not an exact supplier of (IV.5). |

**Correspondence 8.2 (mature allocation and enumeration).** Finite
prefix-subtree sets are laminar: two intersecting prefix subtrees are
nested. Fife and Oxley,
[*Laminar Matroids*, arXiv:1606.08354v1](https://arxiv.org/html/1606.08354v1),
abstract and introduction, give the capacity-defined independent-set
framework for laminar families. Thus finite laminar capacity allocation
is mature mathematics. The descent and ordering argument inside Theorem
2.1 is not a new generic matroid theorem; it supplies the particular
floor quotas, token lower bounds and strict-ancestor slack needed by the
native simultaneous induction.

Cover, [*Enumerative Source Encoding* (1973)](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf),
§I Propositions 1–2 and its inverse algorithm,
[doi:10.1109/TIT.1973.1054929](https://doi.org/10.1109/TIT.1973.1054929),
supplies finite set indexing and inversion. Enumeration and pigeonhole
counting are not new claims. They alone do not provide literal-prefix
coherence over the native predecessor partition.

Seroussi and Weinberger,
[arXiv:1412.2192v1, Procedure E1 and Theorem 1](https://arxiv.org/html/1412.2192v1),
use type-class indexing for universal fixed-to-variable random-number
generation and expected output-length optimality. Zhou and Bruck,
[arXiv:1209.0730v1, the status-tree construction and Definition 1](https://arxiv.org/html/1209.0730v1),
retain a status tree for streaming unbiased output. Kaspi and Merhav,
[arXiv:1301.0079v1, the zero-delay contract and Theorem 1](https://arxiv.org/html/1301.0079v1),
use causal instantaneous coding in a rate/distortion setting. Their
probabilistic objectives, retained states or instantaneous-code contracts
are different from this full-fibre complete-word worst-case recovery
problem; those statements do not establish (IV.5).

The repo-derived increment is the simultaneous native floor-quota
construction, its exact per-source complete-word minimax consequence,
and the conditional mapping to the unchanged acquired service and four
returned expressions. The suppliers above do not state that conjunction.
This is a source-specific synthesis, with no worldwide-priority or
exhaustive-literature claim. The proofs are ordinary mathematical
arguments; no new Lean declaration or kernel certification is asserted.
The weaker ceiling guarantee, installed rewriting/ordinal/weighted
alternatives and fixed-width obstruction retain their respective scopes.

## 追加锚（本行以下为增补区）
