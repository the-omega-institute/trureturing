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

## 9. Forward recovery without observing the journal end

**Definition 9.1 (the source-conditioned head contract).** Retain
Definition 1.1's entire known-alpha native domain, actual beta-left
operations and complete fibres. In §§9–12, $J$ denotes an alternative
binary recorder, rather than the end-visible recorder of §§1–8. It is
injective on every $\mathcal H(t)$ and obeys

$$
J(h)\preceq J(he)
\quad\text{for every enabled extension},\qquad
M_J(t)=\max_{h\in\mathcal H(t)}|J(h)|,\qquad
G(t)=\lceil\log_2F(t)\rceil.
\tag{IV.14}
$$

Only data bits are immutable; this imposes no new immutability on paid
link or header maintenance. The decoder has the actual acquired current
source $t$, the fixed program and common live binding/rights context,
and starts at the fixed installed journal entry. It may acquire successive
data bits in forward order and perform backed finite computation. On every
maintained input $(t,J(h))$, it must halt with the exact full addressed $h$
without requesting a bit beyond that record. No journal end, tail, length,
next-cell absence, timing, capacity, allocator identity or hidden serial
advice is supplied as a stopping observation. A count computed from the
acquired source or the already read bits is permitted; an independently
observed current record length is not. No varying persistent codebook or
chosen entry binding accompanies the record. Off-image inputs have no
additional promised response. In particular this is not an arbitrary-input
trailing-bit validator.

For a fixed finite source fibre and its codebook, this on-image head
contract is equivalent to injection together with prefix freedom:

$$
h,h'\in\mathcal H(t),\quad J(h)\preceq J(h')
\quad\Longrightarrow\quad h=h'.
\tag{IV.15}
$$

Indeed, if distinct histories had words $x\preceq y$, a correct deterministic
decoder on $x$ would have to halt using at most its $|x|$ bits. The same
source and acquired bits on $y$ force the same computation and answer.
Trying an extra read on $x$ would invoke the excluded end/absence channel.
Conversely, follow the finite codebook trie and stop on reaching a codeword.
On-image prefix freedom makes this its unique history; no next-bit test is
needed. An empty word can therefore occur only on a singleton fibre. This
is the usual instantaneous-code argument with the source as side information.

This equivalence is initially one of source-conditioned decision trees.
If $J$ is computable on native histories, it is also effective uniformly:
enumerate the finite $\mathcal H(t)$ by (IV.3), compute all its records in
paid scratch, and construct that trie with one fixed finite program. No
source-dependent table is supplied as advice. Prefix freedom alone for an
arbitrary noncomputable $J$ does not assert a uniform computable decoder.
The lower bound below applies even to such noncomputable recorders.

## 10. A complete-native obstruction at two current sources

**Theorem 10.1 (three continuations force an extra bit at the terminal
source).** Define finite terms by

$$
\begin{aligned}
C_0(x)&=x,& C_{r+1}(x)&=\langle C_r(x),\alpha\rangle,\\
D&=\langle C_2(\beta),\beta\rangle,&
U&=\langle C_{16}(\beta),\beta\rangle,\\
T&=\langle C_{16}(D),\beta\rangle.
\end{aligned}
\tag{IV.16}
$$

Every recorder on the **entire** native domain satisfying (IV.14)–(IV.15)
obeys

$$
\begin{gathered}
F(U)=17,\qquad N(U)=19,\qquad F(T)=63,\qquad N(T)=23,\\
M_J(T)\ge M_J(U)+2\ge7>G(T)=6.
\end{gathered}
\tag{IV.17}
$$

Thus no single such recorder, computable or otherwise, attains the static
prefix-code maximum $G(t)$ at every source. Codewords at one source need
not have a common length.

Proof. All addresses in the proof are logical addresses on the actual
beta-left source. Put

$$
\rho=P_\varepsilon S_\varepsilon,\qquad
A_i=S_{L^i}\ (1\le i\le16),\qquad B=P_R.
\tag{IV.18}
$$

The known alpha first requires its root promotion and root split. The
left child is then beta and the right child alpha. Each $A_i$ splits the
current leftmost beta created by its preceding split; $B$ promotes the
independent right alpha. The source event reconstruction of AA Theorem
17.2 gives precisely these events for $U$: after $\rho$ the only order
constraints are $A_1<\cdots<A_{16}$, with $B$ independent. There are exactly
17 insertion positions for $B$, hence exactly 17 histories, each with
$2+16+1=19$ events. There are no extra promotions at left-born positions,
and no split or promotion elsewhere can disappear from the endpoint.
This identifies the whole fibre, not a selected family of executions.

The current beta at the tip of $U$ is at $p=L^{17}$. Set

$$
X=S_p,\qquad Y=S_{pL},\qquad Z=S_{pLL},\qquad Q=P_{pR}.
\tag{IV.19}
$$

The split $X$ creates a left beta and a right alpha at these actual
positions. Split $Y$ creates the beta on which $Z$ acts; $Q$ promotes the
right alpha created by $X$. Thus the constraints are exactly $X<Y<Z$
and $X<Q$. Each $h\in\mathcal H(U)$ admits the three distinct suffixes

$$
XYZQ,\qquad XYQZ,\qquad XQYZ.
\tag{IV.20}
$$

Every displayed edit is enabled on its actual operand. In each case the
subtree at $p$ becomes $\langle C_2(\beta),\beta\rangle=D$, so the endpoint
is $T$. Conversely these are all continuations from $U$ to $T$: their four
labelled events are exactly the difference of the reconstructed endpoint
event sets. This verifies the native direction $\beta\mapsto
\langle\beta,\alpha\rangle$ at every split, without grafting or exchanging
its two children.

For the full terminal fibre, AA's same reconstruction gives, after
$\rho$, the left chain $A_1<\cdots<A_{16}<X$, then an interleaving of
$Y<Z$ with $Q$, together with the independent outer $B$. There are exactly
three left orders, each containing 20 events. In each order $B$ has 21
insertion positions. Every resulting linear extension is an actual legal
history by AA Theorem 17.2, and its event set has no other members. Hence

$$
F(T)=3\cdot21=63,\qquad N(T)=2+20+1=23.
\tag{IV.21}
$$

Of these histories, precisely those with $B$ before $X$ pass through $U$
after event 19. There are $3\cdot17=51$ of them, exactly the histories
$h$ followed by (IV.20). The other $3\cdot4=12$ place $B$ after $X$;
they belong to the full terminal fibre throughout this argument. The
three suffixes supply inherited demand inside that full fibre, not a
replacement of it.

Use the elementary prefix-cylinder count. If $k$ distinct prefix-free
words extend a word $x$ and have lengths at most $L$, their nonempty sets
of descendants at depth $L$ are disjoint subsets of the $2^{L-|x|}$ slots
below $x$. Consequently

$$
k\le2^{L-|x|}.
\tag{IV.22}
$$

This is the mature finite Kraft/cylinder argument, with no native or
computability hypothesis. Applied at the root to the 17 records at $U$,
it gives $17\le2^{M_J(U)}$, so $M_J(U)\ge5$. Choose a history $h_*$
attaining that finite maximum and put $x=J(h_*)$. Literal preservation
along each of its four-event continuations makes $x$ a prefix of all
three terminal records. They are distinct and prefix-free by (IV.15)
on the full $\mathcal H(T)$. Taking $L=M_J(T)$ in (IV.22) yields
$3\le2^{M_J(T)-M_J(U)}$, hence $M_J(T)\ge M_J(U)+2\ge7$.
Since $32<63\le64$, $G(T)=6$.

For comparison, at a single fixed source the same root count gives the
static lower bound $M\ge\lceil\log_2F\rceil$, and assigning distinct
words of that common length attains it. Such separate static assignments
impose no extension relation between sources. It is their simultaneous
native literal-prefix compatibility that (IV.17) rules out. No equality
of old record lengths, computability, finite horizon, or bound on scratch
work was used. $\square$

## 11. Existing head replay, unchanged service and returned meanings

**Correspondence 11.1 (the supplied ordinal recorder is an upper bound).**
Use AAII §§94–98's existing recorder $J_{\rm ord}$ and complete acquired
service. At event $i$ it appends the actual operand's pre-edit logical-leaf
rank in $d_i=\lceil\log_2L_i\rceil$ padded bits, writing no bits when
$L_i=1$. That construction, its acquired rank scan and its non-atomic
append transaction are unchanged.

Its existing inverse acquires $N(t)=a(t)+2c(t)-1$ from this same current
source, starts in paid scratch at the known alpha, and replays exactly
$N(t)$ events from the journal head. At each iteration the recovered
prefix tree determines $L_i,d_i$; the next $d_i$ bits determine the actual
rank, enabled kind and full address. AAII Theorem 94.2 proves that these
iterations recover $h$ and consume exactly $J_{\rm ord}(h)$. Halting is
by $N(t)$, with no tail read, length comparison, null-next test or
trailing-bit validator. Any append tail or terminal link in its paid
maintenance layout is not passed as a decoding observation.

In particular its records are prefix-free separately on every full
fibre. If two same-source records were prefix-related, the deterministic
$N(t)$ replay iterations on the shorter one would read the same bits
and infer the same events on the longer one. The histories, and therefore
their records, would coincide. Together with its existing literal-prefix
law this shows that the requested class is nonempty, with one computable
horizon-independent member. The supplied all-event-count upper is

$$
M_{J_{\rm ord}}(t)\le B_{N(t)},\qquad
B_0=0,\qquad B_N=\sum_{j=1}^{N-1}\lceil\log_2j\rceil\ (N\ge1),
\qquad B_N\le\log_2(N!)+N.
\tag{IV.23}
$$

This is AAII Proposition 94.3's existing upper, not an attaining code for
(IV.17). Its forced left comb has $F=1$ while its ordinal payload grows,
so it supplies no uniform additive-overhead guarantee relative to $G(t)$.

All actual-source acquisition and completion premises of AA Assumption
20.1, AAII §§95–96 and Assumption 5.1 remain. The genuine known-alpha root,
source/record/input/output bindings, current exclusive rights, finite
backing and supplied finite progress are prerequisites. No erased prefix,
automatic grant, free constructor port, numeric reference cast or hidden
history archive is introduced. Missing rights or a wrong phase disable
a primitive; they are not additional refusal replies.

The reused service has all seven original requests: Tag, addressed $P$
and $S$, HasPromotion, HasSplit, FetchGrowth and Next. AAII Definition
96.1 keeps their complete three-bit tags and address/index frames and all
eight full reply forms: Tag, Boolean, Refusal, Growth, Recall, Next,
OutOfRange and BadFrame with their entire original payloads. Tag reads
the current constructor/absence; HasPromotion tests born-alpha and
non-alpha, HasSplit tests branch, and both are false absent. Absent,
branch and wrong-type growth retain their distinct unchanged-source
refusals. The unused tag gives BadFrame. FetchGrowth and Next have
OutOfRange at $k=0$ or $k>N(t)$, with no growth.

For an in-range FetchGrowth the acquired reply is the literal $k$th
kind and full logical address. Next retains that old pair and its inner
continuation, navigates its historical address on the **same current
live source**, follows actual left logical children through branches,
then executes the uniquely enabled $P$ or $S$ at the reached current
leaf. It acquires this new operand's actual pre-edit rank and appends its
actual new event. Its one complete outer Next reply contains both old
and new pairs; replay supplies no substitute physical operand and no
extra external Recall, return or ACK.

Incomplete ingress retains only the acquired input prefix and backed
parser/pending work; it waits for supplied completion. Reserve, real edit,
append and pending maintenance remain serialized. Each completed outer
request builds and seals its full reply before Print, then emits its
bits and the original reply **End**. The supplied local ACK enables
Return to the same actual root and clearing of occupied request,
traversal, replay, index, append, continuation and output work before
Ready. Excluding a journal-end observation removes none of these reply
and return events. The original finite-service proof is AAII Theorem
96.2; no replacement encoder or newly installed service is asserted here.

**Correspondence 11.2 (the native witness and the four returned views).**
For a concrete consumption of the witness fibre, both

$$
h_0=\rho B A_1\cdots A_{16},\qquad
h_1=\rho A_1B A_2\cdots A_{16}
\tag{IV.24}
$$

end at $U$. FetchGrowth$(3)$ returns $P_R$ and $S_L$, respectively.
On that current $U$, Next$(3)$ actually executes $S_R$ and $S_{L^{17}}$,
respectively: $R$ is a present beta leaf, whereas $L$ is a branch whose
leftmost present logical leaf is at $L^{17}$. Thus the indexed serial
choice affects both a complete reply and a real next source edit, even
though the current source geometry and causal partial order agree.

Precisely on the ordinal installation's actual returned image, AAII
Theorem 97.2 identifies the supplemented views $(S_0,J_{\rm ord})$,
$(B_0,J_{\rm ord})$, successful time $h$, and callable memory consisting
of this retained source, bound journal and fixed driver with current
rights. Here $S_0,B_0$ are AA Definition 17.3's oriented material support
and terminal antichain, including unary beta markers. Prefix closure,
maximal elements and arity parsing give $S_0\leftrightarrow B_0
\leftrightarrow t$ and hence the reconstructed causal order. Head replay
then gives the chosen serial $h$. Conversely native replay of $h$ gives
$t$, both source views and its ordinal bits. These routes factor through
the same $(t,h)$ and commute with the supplied complete seven-request
service; (IV.24) excludes the corresponding bare-geometry serial inverse.
They identify semantic contents on that acquired image, and create no
absent reference, backing or authority.

All costs remain separate: source vertices and fields, headers and links,
reference widths and actual bindings, licensed scans/reads/writes and
edits, rank arithmetic and scratch replay, reservations and coexisting
old/new work, ingress and pending state, complete output, Print, End,
ACK, root Return, clearing and retained cleared capacity. A charged
additional observable serial channel would still change the conditioning;
payment alone does not erase its information. Successful time here means
literal generation order, not physical duration, queries/refusals,
controller chronology or the entire I/O history. No busy-cut inverse,
crash recovery, unknown late-history initialization or physical total-cost
optimum follows.

## 12. Supplier subtraction and the open redundancy question

**Correspondence 12.1 (the source-specific increment).** AA §§17–22 supply
the original source, full history/linear-extension domain, shuffle
reconstruction, source-derived event count, support/boundary parsing and
all acquired service/return hypotheses. AAII §§75–83 supply static
enumerative rank and its rewriting service; §§94–98 supply the ordinal
recorder and service reused in §11. These are not new coding or service
constructions. The repository's
[PrefixFreeCode](../../../D5/S0/Computability/Coding/PrefixFreeCode.lean)
(first-codeword uniqueness, empty-word degeneracy and finite Kraft),
[KraftConverse](../../../D5/S0/Computability/Coding/KraftConverse.lean),
and the immutable-extension suppliers already listed in Correspondence
8.1 concern mature static prefix/cylinder capacity or adjoining words
incomparable with frozen codewords. Here the old word must instead prefix
its own later histories at different native sources. No fresh compilation
of those declarations is asserted.

Cover's primary [*Enumerative Source Encoding*, §I, Propositions 1–2 and
inverse algorithm](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf)
indexes a finite set of fixed-length words over a finite alphabet. For
one $t$, take that set to be the complete $\mathcal H(t)$: event labels
range over its finite addressed event alphabet and every history has
length $N(t)$. This supplies static indexing and inversion, with no
constraint relating the records of $h$ and $he$ at different sources.

Alon and Orlitsky's primary [*Source Coding and Graph Entropies*,
§§1.1–1.3, pp. 1–3](https://web.math.princeton.edu/~nalon/PDFS/entropies3.pdf)
defines restricted-input zero-error messages to be unequal and
non-prefix-related on confusable inputs. Take $X=h$, $Y=t(h)$ and support
$\{(h,t(h))\}$, with any full-support distribution on the countable native
histories. Confusability is then exactly equality of the current source,
so their restricted-input condition is (IV.15). Their unrestricted-input
condition requires global prefix freedom, which is not imposed here.
Their static/expected-length and independent-block objectives do not
impose native literal-prefix coherence or the simultaneous per-source
maximum criterion of (IV.17). The side-information/prefix principle,
like the cylinder count (IV.22), is mature mathematics.

The repo-derived increment is the explicit complete-native $17/63$
contradiction: every old history has three actual continuations, yet the
full terminal fibre still has static width six. Neither prefix/Kraft
counting, shuffle reconstruction, static ranking nor the existing service
is presented as a new general theorem. This is a source-specific ordinary
mathematical proof, with no worldwide novelty or fresh Lean/kernel claim.
The end-visible optimum of §§1–8 allows prefix-related terminated words;
AAII §100 instead assumes exact source widths; AAII §99 reads its weighted
predecessor records from the tail. Their hypotheses and conclusions keep
their stated scopes, and none supplies the forward bridge excluded here.

**Question 12.2 (uniform redundancy).** For the coherent fibrewise
prefix-free class put

$$
\Delta(J)=\sup_{t\in\mathcal D}\bigl(M_J(t)-G(t)\bigr).
\tag{IV.25}
$$

Theorem 10.1 gives $M_J(T)-G(T)\ge1$ for every member, hence
$\inf_J\Delta(J)\ge1$; this remains true if the infimum is restricted to
computable members. Whether one computable horizon-independent recorder
has $\Delta(J)\le1$, or even $\Delta(J)\le C$ for some universal finite
constant $C$, remains unresolved here. The ordinal upper (IV.23) is not
such a bound. Its own large comb redundancy does not prove unbounded
necessary redundancy for all recorders. Neither a seven-bit attaining
recorder at $T$, a minimum witness horizon nor a sharp general redundancy
law is asserted. The broader mutual-recovery and minimal-generator
programme is not settled by this finite native obstruction.

## 追加锚（本行以下为增补区）

## 13. Nested native blocks and their complete endpoint fibres

**Definition 13.1 (blocks on the actual left beta spine).** Retain the
entire domain and head-observation contract of Definition 9.1. With
$C_j(x)$ as in (IV.16), for $d\ge1$ put

$$
\begin{aligned}
D_d(x)&=\langle C_{d-1}(x),\beta\rangle,\\
q_0&=0,\qquad q_i=\sum_{j=1}^i d_j,\\
t_0&=\beta,\qquad
t_i=D_{d_1}(D_{d_2}(\cdots D_{d_i}(\beta)\cdots))
\quad(1\le i\le r),
\end{aligned}
\tag{IV.26}
$$

where $r\ge1$ and $d_1,\ldots,d_r$ are positive integers. These $d_i$
count splits, not ordinal-code widths. The deepest left beta of $t_i$
is at $L^{q_i}$. Each expression specifies an endpoint term; $D_d$ is
not an added graft operation. All constructions below use only (IV.1).

**Proposition 13.2 (the full native product, including delayed
promotions).** For every such vector of block lengths, the complete
fibre of $t_r$ has

$$
\begin{aligned}
F(t_r)&=\prod_{i=1}^r
 \left(\sum_{j=i}^r d_j+r-i\right),\\
a(t_r)&=q_r-r,\qquad c(t_r)=r+1,\qquad
N(t_r)=q_r+r+1.
\end{aligned}
\tag{IV.27}
$$

Every member of this fibre is an admitted native history, including
histories that do not pass through one or more selected $t_i$.

Proof. Write the actual addressed events as

$$
\rho=P_\varepsilon,\qquad
A_j=S_{L^{j-1}}\ (1\le j\le q_r),\qquad
Q_i=P_{L^{q_{i-1}}R}\ (1\le i\le r).
\tag{IV.28}
$$

There are $q_r$ branches, all on the left spine. The right child born
at its $(q_{i-1}+1)$st split is a final beta leaf, requiring exactly
$Q_i$. Every other right child remains alpha, and the deepest left leaf
is born beta. Thus AA Theorem 17.2 reconstructs exactly the displayed
event set, with generating relations

$$
\rho<A_1<\cdots<A_{q_r},\qquad
A_{q_{i-1}+1}<Q_i\quad(1\le i\le r).
\tag{IV.29}
$$

The $Q_i$ have no successors. There is no promotion at a left-born
position, no right split, and no additional event that can disappear
from the final term. Conversely every linear extension of (IV.29) is
legal at every prefix and ends at $t_r$, by that same source theorem.
In particular this identifies the full native fibre without restricting
the schedule to block-completed histories.

Remove the forced first event $\rho$. Remove $Q_1,Q_2,\ldots,Q_r$ in
that order to count the extensions. In the reduced order with
$Q_1,\ldots,Q_i$ absent, every remaining promotion $Q_j$, $j>i$, is
anchored strictly after $A_{q_{i-1}+1}$. The latter split therefore has
position $q_{i-1}+1$ in every extension of that reduced order. Its word
has length $q_r+r-i$. Reinserting $Q_i$ has precisely

$$
(q_r+r-i)-(q_{i-1}+1)+1
=q_r-q_{i-1}+r-i
\tag{IV.30}
$$

slots after its anchor, including immediately after the anchor and at
the end. Each slot is legal, since this is $Q_i$'s only prerequisite
apart from the already forced split ancestors, and it has no successors.
Deletion and insertion are inverse operations. Hence the number of
extensions before each deletion is the constant (IV.30) times the
number after it. After all deletions only the one split-chain order
remains. Multiplication proves the first line of (IV.27).

Equivalently, for the beta-born suffix terms $x$ in (IV.26), AA Theorem
19.2's local shuffle product gives
$F(D_d(x))=(d+e_\beta(x))F(x)$: the left child has
$d-1+e_\beta(x)$ events and the right beta child has its one promotion.
Also $e_\beta(D_d(x))=d+1+e_\beta(x)$ and $e_\beta(\beta)=0$.
These identities give the same factors, retaining the events in all
deeper blocks rather than multiplying conditional suffix counts.

Each split increases the leaf count by one and preserves the beta-leaf
count; $\rho$ and the $r$ right promotions give $r+1$ beta leaves.
Thus the remaining $q_r-r$ leaves are alpha and the native event count
is $q_r+r+1$, also directly visible in (IV.28). For example,
$(d_1,d_2)=(3,2)$ gives $F(t_2)=6\cdot2=12$. Only
$3\cdot2=6$ histories finish the first block before entering the second;
the other six delay $Q_1$ beyond that cut. The product
$\prod_i d_i$ counts just such block-completed concatenations, not the
complete endpoint fibre. $\square$

## 14. Inherited cylinders along actual source cuts

**Theorem 14.1 (rounded depth is paid at every selected cut).** Every
recorder on the full native domain satisfying (IV.14)–(IV.15), whether
computable or not, obeys

$$
M_J(t_r)\ge M_J(\beta)+
 \sum_{i=1}^r\lceil\log_2d_i\rceil
\ge\sum_{i=1}^r\lceil\log_2d_i\rceil.
\tag{IV.31}
$$

No common word length at a source, per-event code, block delimiter or
prefix freedom across different sources is assumed.

Proof. At $t_{i-1}$ put $p=L^{q_{i-1}}$. Its current subtree at $p$
is beta. The new splits are
$S_p,S_{pL},\ldots,S_{pL^{d_i-1}}$, in that forced order, and its new
promotion is $Q_i=P_{pR}$. The first split creates the actual right
alpha on which $Q_i$ acts. For each $k\in\{1,\ldots,d_i\}$ the suffix

$$
v_{i,k}=
 \left(\prod_{j=0}^{k-1}S_{pL^j}\right)
 P_{pR}
 \left(\prod_{j=k}^{d_i-1}S_{pL^j}\right)
\tag{IV.32}
$$

is legal, with products denoting concatenation in increasing $j$ and
an empty product denoting the empty word. The first split uses the
current beta at $p$; each subsequent split uses the beta born to the
left of the preceding split. $Q_i$ leaves those operands unchanged.
All $d_i$ suffixes have $d_i+1$ events and end at
$t_i$. Every $h\in\mathcal H(t_{i-1})$ admits every one of them:
all events of its current source are complete, independently of their
earlier serial order. These are distinct actual extensions, and are
exactly the extensions from this cut to $t_i$ because they contain
precisely the difference of the two endpoint event sets. Their use
does not exclude other histories in $\mathcal H(t_i)$.

The finite nonempty fibre at $t_{i-1}$ has a history $h_*$ attaining
$M_J(t_{i-1})$. Literal prefix preservation at each enabled edit makes
$x=J(h_*)$ a prefix of all $J(h_*v_{i,k})$. Those $d_i$ words are
distinct and prefix-free in the full fibre at $t_i$. Apply the mature
binary-cylinder bound (IV.22), with $L=M_J(t_i)$. After stripping $x$,
their depth-$L-|x|$ cylinders are disjoint and nonempty, so

$$
d_i\le2^{M_J(t_i)-M_J(t_{i-1})},\qquad
M_J(t_i)\ge M_J(t_{i-1})+\lceil\log_2d_i\rceil.
\tag{IV.33}
$$

This includes $d_i=1$ and an empty residual word. Summing these
inequalities and using $M_J(\beta)\ge0$ proves (IV.31). The maximizing
history may depend on $J$ and on the cut. No nested choice of maximizing
histories is needed, since every history at each cut admits the displayed
suffixes. The old bits may have been delayed or encoded jointly in any
way; only their literal preservation and terminal fibrewise prefix
freedom were used. $\square$

## 15. No finite uniform additive redundancy at the head

**Theorem 15.1 (a recorder-independent unbounded native family).** For
each integer $r\ge1$ choose

$$
d_i=8^{r-i+1}+1\quad(1\le i\le r),\qquad
T_r=t_r,\qquad B_r=\frac{3r(r+1)}2.
\tag{IV.34}
$$

This is one explicit computable family of actual finite native sources,
independent of the recorder. For every $r\ge1$ and every full-domain
$J$ satisfying (IV.14)–(IV.15),

$$
\begin{aligned}
M_J(T_r)&\ge B_r+r,\\
G(T_r)&\le B_r+\lceil r/2\rceil,\\
M_J(T_r)-G(T_r)&\ge\lfloor r/2\rfloor.
\end{aligned}
\tag{IV.35}
$$

Consequently $\Delta(J)=+\infty$ for every such recorder. In particular
there are no finite universal $C\ge0$ and single deterministic computable
horizon-independent recorder, with $J(\varnothing)=\varepsilon$ and the
stated head decoder, satisfying $M_J(t)\le G(t)+C$ at every actual source.
The same negative conclusion holds without a computability assumption.

Proof. For $m\ge1$,
$2^{3m}<8^m+1\le2^{3m+1}$, so
$\lceil\log_2(8^m+1)\rceil=3m+1$. Theorem 14.1 gives
$M_J(T_r)\ge\sum_{m=1}^r(3m+1)=B_r+r$.

Reindex the exact complete-fibre product (IV.27) by $m=r-i+1$:

$$
F(T_r)=\prod_{m=1}^r f_m,\qquad
f_m=\sum_{k=1}^m8^k+2m-1.
\tag{IV.36}
$$

For all $m\ge1$ one has $f_m\le(5/4)8^m$. Indeed $f_1=9\le10$.
For $m\ge2$, the induction hypothesis gives

$$
\begin{aligned}
f_m&=8^m+f_{m-1}+2\\
&\le\frac{37}{32}8^m+2
 \le\frac54\,8^m,
\end{aligned}
\tag{IV.37}
$$

where the last inequality uses $2\le(3/32)8^m$, valid already at
$m=2$ and preserved as $m$ increases. Therefore

$$
F(T_r)\le(5/4)^r2^{B_r}<2^{B_r+r/2},
\qquad G(T_r)\le B_r+\lceil r/2\rceil,
\tag{IV.38}
$$

using $(5/4)^2=25/16<2$ and $r\ge1$. Combining the two bounds proves
(IV.35), since $r-\lceil r/2\rceil=\lfloor r/2\rfloor$.

The quantifier order is $\forall r\ge1\ \forall J$: the same $T_r$
works for every admissible $J$. Only the history attaining its maximum
may depend on $J$. For any finite real $C\ge0$, take
$r=2(\lfloor C\rfloor+1)$. Then
$\lfloor r/2\rfloor>C$, and this $T_r$ violates the proposed bound for
every such recorder. Thus even allowing a choice of recorder after
choosing $C$ cannot help. The argument neither bounds just one recorder
nor fixes a finite future horizon. It does not use the normalization at
the empty history, and hence also excludes the normalized subclass.
This answers Question 12.2's finite-$C$ question by an all-parameter
ordinary mathematical proof. $\square$

## 16. Returned-cut acquisition and the four recovery expressions

**Correspondence 16.1 (the original source and service conditioning).**
For every finite $r$, the family (IV.34) starts at the same known alpha,
uses its forced actual root promotion, and then only the beta-left
splits and right-born promotions (IV.28). Its counts are
$a=q_r-r$, $c=r+1$, $N=q_r+r+1$. The native reachability and legality
argument applies to the entire complete fibre, not just the histories
passing through the selected cuts. AA Assumption 20.1, Assumption 5.1
and AAII Theorem 96.2 admit each such finite history by supplying its
ordinary addressed $P/S$ request frames with sufficient finite backing
and finite progress. Material may depend on the actual finite execution;
no one fixed finite-capacity device is assumed to realize all $r$.

The genuine source/root reference, bound journal/input/output references,
current exclusive source and record rights, installed finite program
and paid workspace are the same acquired prerequisites as in §11.
Neither a numerical endpoint description nor (IV.36) creates an object
reference or grants access. Missing rights or a wrong phase still disable
the primitive, with no additional refusal reply. The complete original
Tag, $P$, $S$, HasPromotion, HasSplit, FetchGrowth and Next requests,
their eight full reply forms, address/index payloads, absence/type
refusals, OutOfRange and BadFrame cases are exactly those of AAII
Definition 96.1 and Correspondence 11.1.

Each completed request still reserves its real backing, serializes source
edit and record maintenance, builds and seals its whole reply, performs
Print and reply **End**, receives the supplied local ACK, Returns to
that same actual root and clears occupied work before Ready. Incomplete
ingress retains only its acquired prefix and pending backed state until
completion is supplied. Excluding journal end, length and absence as
decoding observations removes none of these reply, acknowledgement or
return events. No busy-cut inverse, interrupt or crash recovery follows.

On this conditioning, a hypothetical alternative installation satisfying
Definition 9.1's binary-only head contract induces a recorder covered by
Theorem 15.1. Its decoder may acquire the current source and compute any
finite source-dependent count or codebook in paid scratch; it still
cannot satisfy a finite uniform additive payload bound. A varying
observable entry, header, capacity, allocator state or other serial
archive would be additional conditioning, as already excluded by that
definition. Paying for such a channel does not make it uninformative.
This implication supplies no new installation: §11's acquired ordinal
service remains the existing computable member of the class, with its
stated nonoptimal upper bound.

**Proposition 16.2 (serial distinctions still drive original returned
answers and real Next edits).** The native family contains histories
with the same current geometry and boundary but distinct original
FetchGrowth replies and distinct actual Next edits. More generally every
two distinct histories in $\mathcal H(T_r)$ are separated by an original
FetchGrowth request. Thus the serial distinctions charged in (IV.35)
belong to the unchanged full task.

Proof. Since $d_1\ge9$, the two words

$$
u_0=\rho A_1Q_1A_2\cdots A_{d_1},\qquad
u_1=\rho A_1A_2Q_1A_3\cdots A_{d_1}
\tag{IV.39}
$$

are legal histories of $t_1$. Append to both the same legal concatenation
$v$ of suffixes (IV.32) for blocks $2,\ldots,r$, taking $v=\varepsilon$
when $r=1$. The resulting histories $h_0=u_0v$, $h_1=u_1v$ end at the
same $T_r$. FetchGrowth$(3)$ returns respectively $P_R$ and $S_L$.
On that same current source, $R$ is a beta leaf and the leftmost logical
leaf below $L$ is the beta at $L^{q_r}$. Hence Next$(3)$ executes
respectively $S_R$ and $S_{L^{q_r}}$. These are edits on the actual
current source after the internal recall, not on a historical scratch
tree. The single outer Next reply retains both the old recalled pair
and its actual new pair, followed by the original completion and Return
phases; no external Recall or extra ACK is inserted.

For arbitrary distinct $h,h'\in\mathcal H(T_r)$, their common finite
event count ensures an index $k\in\{1,\ldots,N(T_r)\}$ at which their
literal kinds or full addresses differ. FetchGrowth$(k)$ returns those
different pairs. Thus the full original task must distinguish every
member of the fibre. AA Definition 17.3 still gives
$S_0\leftrightarrow B_0\leftrightarrow T_r$ by arity parsing, prefix
closure and maximal elements, including beta's unary marker. Those bare
source views determine the causal order, and identify neither $h_0$
nor $h_1$ as the selected serial extension. $\square$

On the acquired ordinal installation, AAII Theorem 97.2's inverse routes
between supplemented space $(S_0,J_{\rm ord})$, supplemented boundary
$(B_0,J_{\rm ord})$, successful serial time $h$, and retained callable
memory still factor through the same actual $(t,h)$ and commute with
the complete original service. Theorem 15.1 changes the attainable
payload boundary for a forward head supplement with immutable prefixes:
even the static per-source prefix-code width $G(t)$ plus any fixed
constant cannot suffice uniformly. This does not remove the existing
mutual recovery on the supplemented returned image, and it adds no
serial inverse from bare geometry or boundary. Successful time remains
generation order, excluding physical duration and the wider I/O,
controller, query and refusal chronology.

The charge in (IV.35) is only the maximum number of binary data bits
at a specified current source. Actual source vertices and fields,
journal headers and links, reference widths and bindings, granted
access, scans/reads/writes, edits, arithmetic, scratch replay, reserved
and coexisting old/new backing, ingress and pending work, full output,
Print, End, ACK, root Return, cleanup and retained cleared capacity keep
their separate charges from §11 and AAII Definition 97.3. No total-cost,
runtime, latency, energy or general physical or quantum impossibility
is entailed by this binary observation-contract lower bound.

## 17. Suppliers and the remaining redundancy boundary

**Correspondence 17.1 (repo-derived synthesis and its scope).** The
finite prefix-cylinder inequality used inside Theorem 14.1 is (IV.22),
the mature Kraft counting principle already separated in §12.1 and
represented by the existing PrefixFreeCode and KraftConverse suppliers.
AA Theorems 17.2 and 19.2 supply actual native event legality and complete
shuffle enumeration. Cover's primary
[*Enumerative Source Encoding*, §I, Propositions 1–2 and inverse
algorithm](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf)
supplies static finite-set indexing: here one endpoint's histories have
the common length $N(t)$ over its finite addressed-event alphabet.
Neither that fixed-endpoint indexing nor the static prefix/cylinder
principle imposes simultaneous native literal-prefix coherence.
These ingredients and the acquired service of §11 are reused suppliers.

The additional repo-derived ordinary mathematical synthesis is the
decreasing native block family, its exact complete-fibre product with
all delayed promotions included, and the comparison of the accumulated
integer depth increments with that full product. The $17/63$ obstruction
of Theorem 10.1 retains its stated endpoints and conclusion;
the proof of Theorem 15.1 does not require that certificate. No worldwide
novelty, exhaustive literature coverage or Lean/kernel certification of
the new statements is asserted.

Question 12.2's $\Delta(J)$ is therefore infinite for every member of its
class, including computable members. The sharp attainable unbounded
redundancy as a function of source size or event count is not determined
here. The end-visible complete-word optimum of §§1–8, the rewriting
rank of AAII §§75–83, the backward-readable weighted record of AAII §99,
the exact-width obstruction of AAII §100 and the ordinal upper of §11
retain their respective observation and update contracts. The present
head obstruction supplies no optimal replacement code or global resource
ordering, and the broader space/time/boundary/memory recovery programme
remains open.

## 追加锚（本行以下为增补区）

## 18. Exact inherited-prefix allocation on the full native domain

**本批导航。** 本批增补 §§18–22：先给出带实际标号前驱替换的精确有限分配，再把它递归安装为一个全域前向 head recorder，随后给出 base-4 必要系数和任意 block 的证书上界。它不改判 §§9–17 的既有条目；Question 12.2 的对数级充分性仍开放。

**Definition 18.1 (finite inherited-prefix allocation).** Let $m\ge1$ and let $b_1,\ldots,b_m$ be a finite nonempty labelled multiset of binary words; repetitions are retained as different tokens. A lower word may be empty. For every binary word $q$ put

$$
D_b(q)=\bigl|\{i:q\preceq b_i\}\bigr|,
\qquad
L^*(b)=\max_{\substack{q\text{ binary}\\D_b(q)>0}}
 \left(|q|+\left\lceil\log_2D_b(q)\right\rceil\right).
\tag{IV.40}
$$

The empty word is included among the possible $q$. A completion is a family of distinct words $x_i$ such that $b_i\preceq x_i$ and the family $\{x_i\}$ is prefix-free. The objective is to minimize $\max_{1\le i\le m}|x_i|$. The labels matter in the objective's tie-breaking, even when two lower words coincide.

**Lemma 18.2 (exact finite extension optimum).** Every completion in Definition 18.1 has maximum length at least $L^*(b)$. A completion with maximum length exactly $L^*(b)$ exists. It is obtained by processing tokens in decreasing $|b_i|$, breaking ties by a fixed lexicographic order of their labels, and assigning to each token the lexicographically first unused length-$L^*(b)$ word extending its lower word. Thus $L^*(b)$ is the exact inherited-prefix optimum, not merely a Kraft upper bound.

**Proof.** Put $L=L^*(b)$ and first consider any completion with maximum length at most $K$. For a prefix $q$ with $D_b(q)>0$, at least one completed word extends $q$, so any maximum length $K$ first satisfies $K\ge |q|$. The $D_b(q)$ completed words extending $q$ are distinct and prefix-free. Extend each of them, only for counting, to an arbitrary descendant of length $K$. Their depth-$K$ cylinders below $q$ are disjoint, and there are only $2^{K-|q|}$ such descendants. Hence

$$
D_b(q)\le 2^{K-|q|},\qquad
K\ge |q|+\left\lceil\log_2D_b(q)\right\rceil.
\tag{IV.41}
$$
Taking the maximum gives $K\ge L^*(b)$. This padding is a counting device; it does not alter the completed words.

For sufficiency, assign all words at the common depth $L$. Equation (IV.40) implies $|b_i|\le L$. Suppose the greedy rule fails for the current token $i$. Every one of the $2^{L-|b_i|}$ leaves below $b_i$ is already occupied by an earlier token $j$. Since earlier lower words have $|b_j|\ge|b_i|$ and $b_j\preceq x_j$ while $b_i\preceq x_j$, one has $b_i\preceq b_j$. Therefore

$$
D_b(b_i)\ge 1+2^{L-|b_i|},
$$
contradicting (IV.40) at $q=b_i$. The assignment never fails. Equal-length distinct words are prefix-free, and each extends its own lower word. The prescribed order makes the construction a single finite deterministic algorithm. $\square$

**Definition 18.3 (labelled native substitution).** For a noninitial reachable source $t$, let $\operatorname{Pred}(t)$ be AAII Definition 99.1's complete labelled incoming set. For each edge $e:u\to t$ and each $h\in\mathcal H(u)$, form one token

$$
(e,h)\longmapsto he,\qquad b_{e,h}=J(h).
\tag{IV.42}
$$

The token is retained even when two unlabelled source changes look identical. By the actual last-event partition (IV.3), these are exactly the $F(t)$ histories in the complete fibre, with no selected-schedule restriction. The lower word is the literal old data; it is never replaced by a static rank or a newly chosen entry.

## 19. One computable linear recorder and its forward inverse

**Theorem 19.1 (full-domain inherited-prefix recorder).** There is one deterministic computable, horizon-independent map $J$ on every finite legal native history such that, for every reachable $t$,

$$
\begin{aligned}
J(\varepsilon)&=\varepsilon,\\
J(h)&\preceq J(he) &&(e\text{ enabled after }h),\\
G(t)&\le M_J(t)\le G(t)+N(t)-1 &&(N(t)>0),\\
M_J(t)&=0 &&(F(t)=1),
\end{aligned}
\tag{IV.43}
$$

where $G(t)=\lceil\log_2F(t)\rceil$ and $M_J(t)=\max_{h\in\mathcal H(t)}|J(h)|$. At each source, the displayed $M_J(t)$ is the exact minimum possible maximum length subject to the already fixed inherited words from its labelled predecessors. The current source computes the finite table and its width, so a fixed-head decoder reads exactly $M_J(t)$ forward data bits and recovers the complete addressed history without reading a journal end.

**Proof.** Set $J(\varepsilon)=\varepsilon$. Induct on the native grade $N(t)$. For $t\ne\alpha$, recursively compute all predecessor tables, form the labelled tokens (IV.42), and apply Lemma 18.2. Define every $J(he)$ to be the assigned word and put

$$
L(t)=L^*\bigl((J(h))_{(e,h)}\bigr)=M_J(t).
\tag{IV.44}
$$

The predecessor grade is $N(t)-1$, so the recursion terminates at the known alpha root. The finite event set, complete labelled addresses, integer ceilings, sorting, and leaf selection are all effective. No future endpoint, horizon, compatible-family limit, compactness choice, or source-supplied codebook is consulted. Lemma 18.2 gives literal extension of every old word and injective prefix freedom at the complete current fibre. It also proves the claimed local optimum.

It remains to bound the width. Write $W(u)=2^{L(u)}$ and, with edge multiplicity, $S(t)=\sum_{e:u\to t}W(u)$. For a prefix $q$ of depth $d$, a predecessor table of width $L(u)$ contributes at most $2^{L(u)-d}$ lower words extending $q$ when $d\le L(u)$, and contributes none otherwise. Thus

$$
2^dD_b(q)\le S(t).
\tag{IV.45}
$$
Taking the maximum in (IV.40) gives $L(t)\le\lceil\log_2S(t)\rceil$, hence $W(t)<2S(t)$ unless $S(t)=1$, in which case $W(t)=1$. Since $W(\alpha)=F(\alpha)=1$, (IV.3) and induction on $N$ give

$$
W(t)<2^{N(t)}F(t)\qquad(N(t)>0).
\tag{IV.46}
$$
The empty-prefix term in (IV.40) gives $L(t)\ge\lceil\log_2F(t)\rceil=G(t)$. From (IV.46), $L(t)<N(t)+\log_2F(t)\le N(t)+G(t)$; integrality yields the upper inequality in (IV.43). If $F(t)=1$, positivity of (IV.3) forces one incoming edge from a singleton predecessor. Induction gives its lower word $\varepsilon$, so (IV.40) gives $L(t)=0$.

For recovery, acquire the actual current source $t$ and its common bindings and rights. Compute the same finite predecessor tree and table in paid scratch, then read exactly $L(t)$ bits from the fixed installed head. The table is injective, so the bits select exactly one $h$. A singleton table reads no bit. For an enabled actual edge $e:t\to v$, compute the prospective finite table in scratch and append the suffix of $J(he)$ after the already present literal prefix $J(h)$. This syntax calculation is not an observation of a future live source, and all temporary tables may be cleared after their charged finite use. No end, absence, length, tail, timing, allocator, or persistent codebook observation is used. $\square$

**Example 19.2 (the first nontrivial native fibre).** At
$t^*=\langle\langle\beta,\alpha\rangle,\beta\rangle$, the complete histories are
$P_\varepsilon S_\varepsilon P_R S_L$ and
$P_\varepsilon S_\varepsilon S_L P_R$. The two incoming lower words at this endpoint are empty, so the rule assigns the distinct one-bit words $0$ and $1$ in the fixed event order. FetchGrowth$(3)$ therefore returns $P_R$ or $S_L$; on the same current source, Next$(3)$ executes $S_R$ or $S_{L^2}$, respectively, while the original full reply, End, supplied ACK and Return phases remain unchanged. This is a concrete native recovery of a serial distinction, not a static endpoint rank.

**Correspondence 19.3 (unchanged original service).** The recorder in Theorem 19.1 is installed only in the data-payload slot of the existing acquired service. The genuine source/root reference, fixed program, exclusive rights, acquired record/input/output bindings, finite paid backing and progress obligations remain those of Assumption 5.1 and §11. All seven original requests—Tag, addressed $P$, addressed $S$, HasPromotion, HasSplit, FetchGrowth and Next—and the complete Tag, Boolean, Refusal, Growth, Recall, Next, OutOfRange and BadFrame replies remain in force. FetchGrowth and Next use the recovered full addressed history and the same current live source; Next retains both old and new recalled pairs and performs the actual new edit. Every completed request still reserves backing, serializes edit and record maintenance, builds and seals its full reply, emits Print and End, receives the supplied local ACK, Returns to the same actual root and clears occupied work. The construction adds no reset, hidden archive, free reference, extra refusal, interrupt, crash recovery or journal-end channel. This is conditional finite service under the unchanged rights and backing hypotheses; it is not a bound on total physical cost, computation, latency or capacity.

**Definition 19.4 (actual inherited-prefix congestion).** Fix the single event order and recursive recorder $J$ of Theorem 19.1. For every noninitial reachable source $t$, use its actual labelled predecessor words, with their full multiplicities, to define

$$
\begin{aligned}
D_t(q)&=\sum_{e:u\to t}
 \bigl|\{h\in\mathcal H(u):q\preceq J(h)\}\bigr|,\\
C(t)&=\max_{\substack{q\text{ binary}\\D_t(q)>0}}
 \frac{2^{|q|}D_t(q)}{F(t)}.
\end{aligned}
\tag{IV.46a}
$$

Set $C(\alpha)=1$. The maximum is over the finite nonempty set of prefixes of these actual lower words. In particular $D_t(\varepsilon)=F(t)\ge1$ and $C(t)\ge1$. Equal lower words on different labelled tokens remain separate contributions. The words in (IV.46a) are the ones already chosen recursively by $J$, not independently optimized codebooks at each endpoint, static ranks, or words chosen for a future horizon.

**Proposition 19.5 (exact width and the missing uniform condition).** For this fixed recorder, at every reachable source,

$$
\begin{aligned}
L(t)&=\left\lceil\log_2\bigl(F(t)C(t)\bigr)\right\rceil,\\
F(t)C(t)&\le 2^{L(t)}<2F(t)C(t),\\
0&\le L(t)-G(t)\le\left\lceil\log_2C(t)\right\rceil.
\end{aligned}
\tag{IV.46b}
$$

A sufficient all-source inherited-prefix congestion condition for the original logarithmic target is the existence of fixed finite constants $K\ge1$ and $a\ge0$, independent of $t$, such that

$$
C(t)\le K\bigl(N(t)+2\bigr)^a
\qquad\text{for every reachable actual source }t.
\tag{IV.46c}
$$

Under this condition the same deterministic computable horizon-independent $J$ satisfies

$$
\begin{aligned}
M_J(t)=L(t)
 &\le G(t)+\left\lceil\log_2K+a\log_2(N(t)+2)\right\rceil\\
 &\le G(t)+a\log_2(N(t)+2)+\log_2K+1\\
 &\le G(t)+c\log_2(N(t)+2),
 \qquad c=a+\log_2K+1.
\end{aligned}
\tag{IV.46d}
$$

Conversely, if this fixed $J$ satisfies $L(t)\le G(t)+c\log_2(N(t)+2)$ at every actual source for one finite $c\ge0$, then

$$
C(t)\le\frac{2^{L(t)}}{F(t)}
 \le\frac{2^{G(t)}}{F(t)}\bigl(N(t)+2\bigr)^c
 <2\bigl(N(t)+2\bigr)^c.
\tag{IV.46e}
$$

Thus polynomial congestion and logarithmic overhead are equivalent uniform growth conditions for this particular recursively chosen recorder. Finite constants may be enlarged to computable integers without changing either existence assertion; no such constants are needed to run the already specified algorithm.

**Proof.** For noninitial $t$, let $A=\max_{D_t(q)>0}2^{|q|}D_t(q)$. The maximum exists by Definition 19.4 and equals $F(t)C(t)$. Since each $|q|$ is an integer, (IV.40) and (IV.44) give

$$
L(t)=\max_{D_t(q)>0}\left\lceil\log_2\bigl(2^{|q|}D_t(q)\bigr)\right\rceil
 =\left\lceil\log_2A\right\rceil.
$$

Consequently $A\le2^{L(t)}<2A$. The ceiling inequality $\lceil x+y\rceil\le\lceil x\rceil+\lceil y\rceil$, with $x=\log_2F(t)$ and $y=\log_2C(t)$, proves the upper bound on $L-G$; its lower bound is Theorem 19.1. At the initial source, $F=1$, $C=1$ and $L=G=0$, so the same conclusions hold. Singleton native fibres also have $C=1$: their actual inherited words are empty by Theorem 19.1. This does not exclude empty lower words from the finite allocation problem.

Substitute (IV.46c) into the exact first identity of (IV.46b) and use $\lceil x+y\rceil\le\lceil x\rceil+\lceil y\rceil$ again to obtain the first line of (IV.46d). A ceiling adds less than one, and $\log_2(N+2)\ge1$ absorbs the displayed nonnegative constant $\log_2K+1$, proving the other lines. Equation (IV.46e) follows from (IV.46b), the assumed bound on $L$, and $2^{G(t)}/F(t)<2$. These estimates retain the distinction between $\log_2F$, its ceiling $G$, the exact width ceiling, and the additive constant in (IV.46d). $\square$

The all-source polynomial condition (IV.46c) remains unproved. The linear argument (IV.46) supplies only $C(t)<2^{N(t)}$ for $N(t)>0$, not a polynomial bound. Proving (IV.46c) would settle logarithmic sufficiency by this construction under the unchanged source, rights, paid scratch and complete-service hypotheses of Correspondence 19.3. Failure of every polynomial bound for this chosen $J$ would rule out logarithmic overhead for this $J$ only; it would not rule out another deterministic computable coherent recorder. Likewise (IV.46c) is not asserted necessary for the existence of a different recorder. A universal-class negative answer would still require an obstruction applying to every admissible recorder on the original full native domain.

## 20. A necessary logarithmic coefficient from the base-4 family

**Theorem 20.1 (base-4 coefficient for every coherent head recorder).** For $r\ge1$, use the native block terms of Definition 13.1 with

$$
 s_i=4^{r-i+1}+1,\qquad T_r=t_r,\qquad B_r=r(r+1).
\tag{IV.47}
$$

Then, for every recorder satisfying Definition 9.1 on the entire native domain,

$$
M_J(T_r)-G(T_r)>r\log_2(3/2)-2.
\tag{IV.48}
$$

Consequently, if some such recorder satisfied
$M_J(t)\le G(t)+c\log_2(N(t)+2)$ for all actual endpoints, then necessarily

$$
 c\ge\kappa:=\frac12\log_2(3/2).
\tag{IV.49}
$$
This is a necessary coefficient only; it supplies neither logarithmic sufficiency nor sharpness.

**Proof.** The complete native product in Proposition 13.2, reindexed by $m=r-i+1$, is

$$
F(T_r)=\prod_{m=1}^r f_m,\qquad
 f_m=\sum_{k=1}^m4^k+2m-1
 =\frac43\,4^m+2m-\frac73.
\tag{IV.50}
$$
At the $i$th selected cut, every old history has $s_i$ actual suffixes: perform the left-spine splits at $p,pL,\ldots,pL^{s_i-1}$ and promote the right child born at the first split at $pR$. The promotion can be inserted after any one of the $s_i$ splits. These are legal native $S$ and $P$ events, and the full endpoint fibre still includes every delayed interleaving. The cylinder argument (IV.22), iterated as in Theorem 14.1, gives

$$
M_J(T_r)\ge\sum_{m=1}^r\left\lceil\log_2(4^m+1)\right\rceil
=B_r+r.
\tag{IV.51}
$$
For every $m\ge1$,

$$
 f_m\le\frac43\,4^m\left(1+\frac{3m}{2}4^{-m}\right).
\tag{IV.52}
$$
Using $\ln(1+u)\le u$ and $\sum_{m\ge1}m4^{-m}=4/9$ gives

$$
\log_2F(T_r)
 \le B_r+r\log_2(4/3)+\frac{2}{3\ln2}
 <B_r+r\log_2(4/3)+1,
\tag{IV.53}
$$
where $\ln2>2/3$. Since $G=\lceil\log_2F\rceil$, (IV.53) implies
$G(T_r)<B_r+r\log_2(4/3)+2$. Combining this with (IV.51) proves (IV.48).

The endpoint has

$$
N(T_r)=\frac{4^{r+1}-4}{3}+2r+1,
\tag{IV.54}
$$
so $\log_2(N(T_r)+2)/r\to2$. Divide (IV.48) by this quantity and let $r\to\infty$ to obtain (IV.49). Every displayed continuation is an actual addressed operation of (IV.1); no deletion, graft, restricted schedule, extra observation or fixed finite-capacity device is used. $\square$

## 21. The arbitrary-block rounded-depth certificate

**Definition 21.1 (certificate separated from recorder redundancy).** For any positive block list $s_1,\ldots,s_r$, let

$$
T=T(s_1,\ldots,s_r),\qquad
N=1+\sum_{i=1}^r(s_i+1),\qquad
f_i=\sum_{j=i}^rs_j+r-i,
$$

so that Proposition 13.2 gives $F(T)=\prod_i f_i$. Define

$$
L_{\rm cut}=\sum_{i=1}^r\left\lceil\log_2s_i\right\rceil,\qquad
E=\max\{0,L_{\rm cut}-G(T)\}.
\tag{IV.55}
$$
The number $E$ is the excess forced by this selected-cut lower-bound certificate after comparison with the static endpoint width. It is a lower bound on $M_J(T)-G(T)$ for every admissible $J$; it is not the actual redundancy of Theorem 19.1 or of any other recorder.

**Theorem 21.2 (uniform ceiling on the certificate).** Let $\gamma$ be the unique positive solution of

$$
(1+\gamma)^{1+\gamma}=2\gamma^\gamma.
\tag{IV.56}
$$
Then $0<\gamma<1/3$, and every positive block list satisfies

$$
E\le\gamma\log_2N.
\tag{IV.57}
$$
Thus changing the block sizes inside this certificate mechanism cannot produce a superlogarithmic all-recorder obstruction. Equation (IV.57) says nothing about an upper bound on actual recorder redundancy.

**Proof.** The function
$\phi(a)=(1+a)\ln(1+a)-a\ln a$ is strictly increasing for $a>0$, tends to $0$ as $a\downarrow0$, and satisfies $\phi(1/3)>\ln2$ because
$(4/3)^4/(1/3)=256/27>8$. Hence (IV.56) has one positive solution and it lies in $(0,1/3)$. The same equation and elementary differentiation give, for $x\ge0$,

$$
2x\le(1+x)^{1+\gamma}.
\tag{IV.58}
$$

Put $d(s)=2^{\lceil\log_2s\rceil}$ and
$R=2^{L_{\rm cut}}/F(T)$. We prove $R\le N^\gamma$ by induction while adding the outer blocks. The empty list has $N=1$ and $R=1$. Suppose the inner tail has event count $n$ and ratio at most $n^\gamma$. Adding an outer block of size $s$ changes the count to
$N_{\rm new}=n+s+1$ and the product factor to $n+s-1$, so

$$
R_{\rm new}=\frac{d(s)R_{\rm tail}}{n+s-1}.
\tag{IV.59}
$$
If $s=1$, then $d(s)=1$ and $R_{\rm new}\le n^{\gamma-1}\le1$. If $s\ge2$, writing $x=(s-1)/n$ and using the integer inequality $d(s)\le2(s-1)$ gives

$$
R_{\rm new}
 \le \frac{2x}{1+x}n^\gamma
 \le (1+x)^\gamma n^\gamma
 = (n+s-1)^\gamma
 \le N_{\rm new}^\gamma,
\tag{IV.60}
$$
where the middle inequality is (IV.58). Consequently

$$
L_{\rm cut}-G(T)\le L_{\rm cut}-\log_2F(T)=\log_2R\le\gamma\log_2N.
$$
Taking the positive part proves (IV.57). The native correspondence is the one in §§13–16: at each block the actual edits are $S_p,S_{pL},\ldots,S_{pL^{s_i-1}}$ and $P_{pR}$, with all complete interleavings retained, and $N=a+2c-1$. $\square$

## 22. Sources, scope and the unresolved logarithmic target

**Correspondence 22.1 (what is reused and what is added).** AA §§17–22 and AAII §99 supply the actual known-alpha grammar, complete labelled predecessor partition, event count, native legality, and the acquired source/rights/service hypotheses. Sections 13–16 supply the complete block fibres and the recorder-independent cylinder lower bound. The new ordinary synthesis is Lemma 18.2's exact inherited-prefix allocation installed recursively in Theorem 19.1, together with its full-domain forward inverse and linear bound (IV.43). Proposition 19.5 identifies the exact actual-word congestion condition sufficient for this same recorder to meet a logarithmic bound; that condition is not established here. The base-4 coefficient (IV.49) and certificate ceiling (IV.57) are separate consequences of the same actual native family; they are not claims that the linear recorder is logarithmic.

Cover's [*Enumerative Source Encoding*, §I, Propositions 1–2 and inverse algorithm](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf) supplies static finite-set indexing only. Kaspi–Merhav's [restricted-input formulation](https://arxiv.org/html/1301.0079v1) supplies the mature side-information/prefix-confusability frame. These sources do not supply literal native inherited-prefix coherence, the original seven-request service, or a worst-endpoint logarithmic bound. No worldwide novelty claim is made, and no inaccessible primary theorem is used as a load-bearing premise.

**Correspondence 22.2 (remaining boundary).** Theorem 19.1 proves existence, computability, horizon independence, actual labelled predecessor substitution, full-fibre prefix freedom and the explicit bound
$G(t)\le M_J(t)\le G(t)+N(t)-1$. Theorem 20.1 proves the necessary coefficient $\kappa$ when a logarithmic estimate exists. Theorem 21.2 shows only that the displayed rounded-depth certificate cannot itself yield a superlogarithmic counterexample. Proposition 19.5 leaves the all-source polynomial bound (IV.46c) for the actual recursively inherited words unproved; success of this constructor is only a sufficient route to existence, and its failure would not be a universal-class impossibility. The original question—one computable $J$ and one finite $c$ satisfying the logarithmic bound for every actual endpoint, or a universal-class counterexample—therefore remains open in this increment. No Lean/kernel verification, numerical result, total-cost optimum, physical impossibility or completion of the persistent RRO goal is asserted.

## 追加锚（本行以下为增补区）

## 23. Native orientation erasure and the pruned tree

**Definition 23.1 (the native quotient and its two fibres).** Use exactly
[AA Definitions 17.1 and 19.1 and Theorems 17.2 and 19.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md):
the known initial $\alpha$, all finite successful addressed words, and
$P_p:\alpha\to\beta$, $S_p:\beta\to\langle\beta,\alpha\rangle$ at a
current leaf, with $\beta$ on the **left**. Write $[t]$ for the finite
rooted unordered full binary tree retaining branch incidence and leaf
colours but forgetting sibling order. Isomorphisms preserve the root and
colours; no vertex identities, clock or physical frames are added. For
such a coloured tree $U$, define

$$
\mathcal O(U)=\{t\in\mathcal D:[t]=U\},\qquad
\mathcal J(U)=\{(t,w):t\in\mathcal O(U),\ w\in\mathcal H(t)\},
\qquad E(U)=|\mathcal O(U)|,\quad J(U)=|\mathcal J(U)|.
\tag{IV.61}
$$

Here $\mathcal D$ and $\mathcal H(t)$ are AA17's exact native domain and
complete $P/S$ histories. Let $K(U)$ be obtained by deleting every
$\alpha$ leaf and its incident edge, retaining the other vertices and
edges, with $K(\alpha)=\varnothing$. Write $n(U)=|K(U)|$. For a rooted
unary/binary tree $K$, let $b(K)$ count its binary vertices, $s(K)$ those
binary vertices with isomorphic rooted child subtrees, $A(K)$ the order
of its rooted automorphism group, and $h_v$ its inclusive descendant
count at $v$. Empty products and $A(\varnothing)$ are one. An increasing
labelling is a bijection $\lambda:V(K)\to\{1,\ldots,|K|\}$ strictly
increasing from parent to child. Write $\mathcal L(K)$ for these
labellings modulo rooted automorphisms, including one empty labelling.

**Proposition 23.2 (exact admissibility and the alpha exception).** The
fibre $\mathcal O(U)$ is nonempty exactly when no branch of $U$ has two
$\alpha$ leaves as children. On this domain $K(U)$ is either empty, for
$U=\alpha$, or a nonempty rooted unary/binary tree. Pruning is a bijection
between these admissible unordered coloured trees and the empty or
rooted unary/binary trees. Its inverse replaces a leaf by $\beta$, a
unary vertex by an unordered branch with its converted child and an
$\alpha$ leaf, and a binary vertex by the branch of its converted
children. If $U$ has $a$ alpha leaves and $c$ beta leaves, then

$$
n(U)=a+2c-1,
\tag{IV.62}
$$

and every history in $\mathcal J(U)$ has exactly this length. In
particular $E(\alpha)=J(\alpha)=1$, with the empty history, while an
inadmissible $U$ has $E(U)=J(U)=0$.

**Proof.** An alpha child must be on the right in AA17's domain. Two alpha
children therefore preclude any native orientation. If every branch has
at most one alpha child, put that child on the right wherever it occurs,
and orient the other branches arbitrarily. The resulting term has no
alpha leaf at an $L$-ending address, hence is reachable by AA17.2. Every
retained branch has one or two retained children, and every retained leaf
is beta. The stated inverse follows recursively; in particular a
zero-child retained branch, which would be confused with beta, is
excluded by admissibility. A full binary tree has $a+c-1$ branches, so
pruning leaves $a+c-1+c$ vertices. Splits number $a+c-1$ and promotions
number $c$, as in AA19.1, proving (IV.62) and the history length. The
single alpha is the only admissible tree with empty pruning. $\square$

## 24. The addressed history and increasing-labelling correspondence

**Theorem 24.1 (endpoint and prefix preserving computable bijection).**
For every admissible $U$ there is a uniform computable bijection

$$
\Phi_U:\mathcal J(U)\longleftrightarrow\mathcal L(K(U)).
\tag{IV.63}
$$

Its forward map attaches the event's one-based position in the actual
word to one newly activated retained vertex: $P_p$ activates $p$, and
$S_p$ activates $pL$, preserving the already active vertex at $p$. Its
inverse orders two children by their root labels, puts a sole child on
the left with alpha on the right, and restores all literal event kinds
and logical addresses. Every initial label segment reconstructs exactly
the corresponding legal source prefix and its guards.

**Proof.** For an actual word, at every prefix prune its current source.
Initially this is empty. A promotion adds the vertex at its alpha leaf;
a split at an active beta leaf keeps that vertex as the parent and adds
its left beta child, while its right alpha child is pruned. Thus every
event adds precisely one vertex, and no active vertex is removed. If the
right child is eventually activated, its first event is its promotion,
strictly later than the split creating the left child. Consequently
parent labels are smaller than child labels, and the earlier of two
child roots is always the left one. Erasing sibling order gives an
increasing labelling of the final $K(U)$. Different identifications with
a fixed representative of $K(U)$ differ exactly by rooted automorphisms,
so the resulting orbit is well defined.

Conversely take an increasing labelling. Restore a final ordered term by
replacing a leaf with beta, a sole child by that child on the left and
alpha on the right, and two children by their increasing root-label
order. All addresses below refer to this restored term. Process the
vertices in label order. For the root execute $P_\varepsilon$. For the
first child $v$ of a vertex $u$, execute $S_{\operatorname{addr}(u)}$;
for its second child execute $P_{\operatorname{addr}(v)}$.

These are actual guarded operations. Before the first child is
processed, $u$ is present as beta: its activating event has occurred,
its split has not, and no descendant can yet be processed. Its split
therefore creates exactly the left beta child and right alpha leaf.
Before the second child is processed, this split has occurred, since
the first child's label is smaller. Its right slot is still alpha:
there is no earlier activation of that child or any of its descendants.
Its promotion is therefore legal. The root case uses the known initial
alpha. No other operation or schedule restriction is required.

More explicitly, for $0\le k\le n$, retain the vertices labelled at most
$k$. This is ancestor closed; at a two-child vertex it contains the
first child whenever it contains the second. Convert this truncated tree
by the same leaf/unary/binary rule, with the empty tree converted to
alpha. Induction on $k$ proves that it is exactly the source after the
first $k$ reconstructed actions. At each such source, $P_p$ is enabled
exactly at its alpha leaves and $S_p$ exactly at its beta leaves; absent
and branch addresses have neither successful operation. Thus all
addressed guards, not just the final shape, agree. This is the concrete
native guard correspondence required to apply
`EnabledPathSwapConnectivity.result`'s finite lower-cut principle, already
supplied for the labelled LAB event order by AA17.2.

Both constructions are inverse: the first child of an actual split has
its split's label, every other activation has its promotion's label, and
root-label ordering recovers exactly those original left/right choices.
Conversely the reconstructed activations reproduce the supplied labels
and incidences. Rooted automorphisms leave this ordered labelled result
and the resulting addressed word unchanged. Finite tree traversal,
comparison of distinct integer labels, and replay implement both maps;
no exposed allocation ordinal or independent serial clock is used.
The increasing-tree convention and ordering siblings by root labels are
classical, as in Bergeron–Flajolet–Salvy,
[*Varieties of Increasing Trees*, Definition 1, §2 and Table 1](https://algo.inria.fr/flajolet/Publications/BeFlSa92.pdf).
The guard argument above identifies that convention with the specified
native $P/S$ operations at every prefix. $\square$

**Corollary 24.2 (symmetry-correct endpoint and joint counts).** For
admissible $U$, put $K=K(U)$ and $n=|K|$. Then

$$
A(K)=2^{s(K)},\qquad
E(U)=\frac{2^{b(K)}}{A(K)}=2^{b(K)-s(K)},\qquad
J(U)=\frac{n!}{A(K)\prod_{v\in K}h_v}
     =\sum_{t\in\mathcal O(U)}F_{PS}(t).
\tag{IV.64}
$$

Equivalently, $J(\alpha)=J(\beta)=1$, and at an admissible unordered
branch $U=\{X,Y\}$,

$$
J(U)=\frac{\binom{n(X)+n(Y)}{n(X)}J(X)J(Y)}
 {1+\mathbf1_{X\cong Y}}.
\tag{IV.65}
$$

If one child is alpha the denominator is one. If both child classes are
equal and non-alpha, the endpoint recurrence is $E(U)=E(X)^2$.

**Proof.** An automorphism acts independently inside the child subtrees,
with an additional factor two precisely at an isomorphic pair. This gives
$A(K)=2^{s(K)}$, the usual rooted symmetry-node decomposition; compare
Kersting–Fischer,
[*Measuring tree balance using symmetry nodes*, §2 and Lemma 3.2](https://arxiv.org/pdf/2105.00719v2).
On a fixed vertex realization of $K$, each binary vertex has two orders
and each unary vertex has its forced left placement. An automorphism
fixing all these orders fixes every vertex, so its action on the $2^b$
choices is free. Their orbits are exactly the native ordered endpoints,
proving the endpoint formula, including equal child classes. The two
positions of an equal pair still admit every ordered pair of internal
representatives, rather than an unordered pair of representatives.

For fixed vertices the classical rooted-tree hook formula counts
$n!/\prod_vh_v$ increasing labellings; see Kuba,
[*A Note on Hook Length Formulas for Trees*, §§3.1–3.2](https://arxiv.org/pdf/1004.1883v1),
also credited in AAII Definition 60.5. Distinct labels make the
automorphism action free. Division by $A(K)$ and Theorem 24.1 prove the
joint formula. Its recursive form is (IV.65), by distributing the labels
other than the root among its child subtrees, with division by two for
an equal pair. The empty case uses $0!=1$. Finally (IV.61) and AA19.2
supply the sum over ordered endpoints. These are computable integer
counts on exactly the admissible domain; GPO22–23's fibre of arbitrary
originals under simultaneous global substitution is a different domain.
For example $\{\beta,\alpha\}$ has two such global representatives but
only the native endpoint $\langle\beta,\alpha\rangle$. $\square$

## 25. Orientation and chronology are coupled by subtree mass

**Theorem 25.1 (constant history fibres exactly at equal masses).** For
admissible $U$, the numbers $F_{PS}(t)$ are constant over
$t\in\mathcal O(U)$ if and only if the two child subtrees at every binary
vertex of $K(U)$ have equal numbers of vertices. Equivalently, every
branch of $U$ with distinct non-alpha child classes $X,Y$ satisfies
$n(X)=n(Y)$. At any legal pair of orientations, with their internal
ordered terms $l,r$ fixed and neither equal to alpha,

$$
\frac{F_{PS}(\langle l,r\rangle)}{F_{PS}(\langle r,l\rangle)}
 =\frac{n([l])}{n([r])}.
\tag{IV.66}
$$

**Proof.** Write $x=n([l])\ge1$, $y=n([r])\ge0$. A non-alpha subtree
born beta differs from the same target born alpha by deletion of its
forced first root promotion, so the two history counts agree. AA19.1–19.2
therefore give

$$
F_{PS}(\langle l,r\rangle)
 =\binom{x+y-1}{x-1}F_{PS}(l)F_{PS}(r).
\tag{IV.67}
$$

For two non-alpha children, interchanging $x,y$ gives (IV.66). For an
alpha child the orientation is forced and the factor in (IV.67) is one.
If the equal-mass condition holds everywhere, induction makes the child
history counts constant on their endpoint fibres, and equal masses make
the two permitted orders have equal factors. This proves sufficiency,
including equal child classes and all unary vertices.

For necessity, take a vertex with unequal positive child masses. Its
child classes are distinct, so both local orders are reachable. Fix all
internal representatives and the rest of one ordered endpoint and swap
only those children. Ancestor factors in (IV.67) depend on unchanged
subtree masses, hence cancel, as do all fixed internal factors. The full
history counts have the unequal ratio $x/y$. They cannot be constant.
Isomorphic children have equal masses automatically, giving the stated
equivalence of conditions. $\square$

**Proposition 25.2 (two endpoints, three histories, different guards).**
For $U=\{\beta,\{\beta,\alpha\}\}$ the complete native endpoint and
history fibres are

$$
\begin{aligned}
t_1&=\langle\beta,\langle\beta,\alpha\rangle\rangle,
&\mathcal H(t_1)&=\{P_\varepsilon S_\varepsilon P_R S_R\},\\
t_2&=\langle\langle\beta,\alpha\rangle,\beta\rangle,
&\mathcal H(t_2)&=\{P_\varepsilon S_\varepsilon S_L P_R,
                    P_\varepsilon S_\varepsilon P_R S_L\}.
\end{aligned}
\tag{IV.68}
$$

Thus $E(U)=2$, $J(U)=3$, and the endpoint projection has fibre sizes one
and two. At $t_1$ the original action $S_L$ is enabled, while at $t_2$
it is refused because $L$ is a branch.

**Proof.** The root prefix is $P_\varepsilon S_\varepsilon$. For $t_1$
the remaining right child must execute $P_R$ before $S_R$. For $t_2$,
$S_L$ and $P_R$ are both enabled immediately after the root prefix and
can occur in either order. AA17.2 excludes any other events, proving the
complete lists. The two child masses are one and two, so (IV.66) also
gives the ratio $1/2$. The final tags at $L$ are beta and branch,
respectively, proving the guard distinction under the original $S$.
$\square$

## 26. Sharp conditional recovery from the native quotient

**Theorem 26.1 (singletons and supplements).** Fix an admissible $U$.
The quotient alone determines the ordered endpoint exactly when
$b(K(U))=s(K(U))$. It determines the full addressed history exactly when
$U=\alpha$, or $K(U)$ is a unary path, or a unary path ending in one
binary vertex whose two children are leaves. A one-vertex tree and a
binary root with two leaves are included in these path conventions.

For any supplied deterministic supplement $q$ on $\mathcal J(U)$,
endpoint recovery is possible exactly when

$$
q(t,w)=q(t',w')\ \Longrightarrow\ t=t',
\tag{IV.69}
$$

and full-history recovery is possible exactly when $q$ is injective.
The sharp numbers of conditional supplement values are respectively
$E(U)$ and $J(U)$; the sharp fixed-width binary content sizes are their
ceiling logarithms. Given the ordered endpoint $t$ as well, the sharp
history supplement has $F_{PS}(t)$ values, as in AA19.2.

**Proof.** The endpoint assertion follows from (IV.64). In (IV.65), a
unary vertex has factor one. A binary vertex with child masses $x,y\ge1$
has factor $\binom{x+y}{x}/(1+\mathbf1_{X\cong Y})$. This equals one
exactly when both children are leaves: if $x+y\ge3$, the binomial is at
least three and the denominator at most two. Thus $J=1$ exactly for the
listed shapes. Equality of supplement values cannot conceal different
target answers, proving necessity of (IV.69) and injectivity. Conversely
these conditions define a decoder on the actual image. At least one
value per distinguishable target is required. Enumerating finite
endpoints, or the labelling orbits of Theorem 24.1 and their inverse
histories, assigns exactly the stated numbers of values. Ranking and
unranking are finite-set indexing, with no extra acquisition premise.
$\square$

**Proposition 26.2 (which relation supplies orientation).** On the full
native fibre, an endpoint-preserving bijection
$\mathcal J(U)\cong\mathcal O(U)\times C$ with one common independent
history alphabet $C$ exists exactly under Theorem 25.1's equal-mass
condition. In general the child-root precedence in the increasing
labelling supplies orientation jointly with chronology, through
Theorem 24.1; the unordered endpoint alone supplies neither that
precedence nor the original addressed guard at every endpoint.

**Proof.** A product over the endpoint projection has $|C|$ histories at
each endpoint, so constant fibre size is necessary. If the sizes are
constant, rank each finite history fibre separately in a common set of
that size, obtaining such a product. Without this condition, orientation
followed by endpoint-conditioned history remains a valid encoding, but
all pairs from independent orientation and chronology alphabets do not:
(IV.68) has two endpoint choices and three joint histories. The inverse
of (IV.63) shows exactly how first-child precedence restores the left
child of a split, including the forced unary case. Distinct labels do
not name physical ports; an automorphism orbit supplies no physical
vertex binding. $\square$

**Definition 26.3 (conditional interface boundary).** These inverses and
rank alphabets describe static mathematical content at a supplied cut.
An acquired interpretation retains AA20's initialized same-source root
binding, current read/write rights, actual backing and work storage,
charged input/output, maintenance, acknowledgement and return to Ready,
and AA21's declared causal or full-generation task. An abstract rank or
labelling orbit supplies none of those hypotheses. In particular this
correspondence installs no paid acquisition service or callable adapter,
provides no physical frame alignment or new grants, and makes no
post-reset survival assertion. Every executable $Q_g$ recovery still
requires the original conditional interface; generation words here
exclude requests, refusals, waiting and controller chronology.

## 追加锚（本行以下为增补区）

## 27. Literal retention for the current ordered term

**Definition 27.1 (current-only recorder and event grade).** Retain
Definition 23.1's known-alpha native domain, its actual addressed guards
$P_p:\alpha\to\beta$ and
$S_p:\beta\to\langle\beta,\alpha\rangle$, and all finite legal histories.
Write $t(h)$ for the endpoint and $U(t)=[t]$ for the rooted coloured
incidence tree with sibling order erased. A recorder assigns a finite
binary word $J(h)$ to every such history, with

$$
J(\varepsilon)=\varepsilon,\qquad
J(h)\preceq J(he),\qquad
\operatorname{Dec}(U(t(h)),J(h))=t(h),
\tag{IV.70}
$$

where $e$ is any actual enabled event and $\preceq$ is literal word
prefix. The complete present word and its end are visible. The decoder
has only these two inputs; no varying retained controller, archive,
address roster, cut markers or advice is available outside $J$. Fixed
code is common to all histories. There is no prefix-free requirement,
no full-history injectivity requirement, and no old-cut recovery task.
For a lower bound, $J$ and the decoder may even be arbitrary semantic
functions satisfying (IV.70); effective attainment will separately
require computable decoding and update from $(U,J,e)$ on the actual image.

Use the successful-event grade
$N(t)=a(t)+2c(t)-1=|h|$, where $a,c$ count alpha and beta leaves, by
(IV.62) and AA19.1. This is not elapsed time, traffic, or an additional
retained event counter. Supplying $U$ in (IV.70) is a mathematical input
contract, not a physical observation port.

**Theorem 27.2 (native reconvergence with every-prefix retention).** Put

$$
C=\langle\beta,\alpha\rangle,\quad
A_0=\langle\beta,C\rangle,\quad
A_1=\langle C,\beta\rangle,\quad
D=\langle C,C\rangle,
\qquad B_0(x)=x,\quad B_{k+1}(x)=\langle B_k(x),B_k(x)\rangle.
\tag{IV.71}
$$

For every recorder (27.1), every $k\ge0$, and **every** legal prefix $h$
ending at $B_k(C)$, some legal continuation $v$ ends at $B_{k+1}(C)$ and
satisfies $|J(hv)|-|J(h)|\ge2^k$. Consequently, for each $n\ge0$ there
is a history at the fixed endpoint $B_n(C)$ with

$$
|J(h)|\ge2^n-1=\frac{N(B_n(C))-2}{3},\qquad
N(B_n(C))=3\cdot2^n-1,\qquad E(U(B_n(C)))=1.
\tag{IV.72}
$$

The witnessing histories can be selected as nested continuations.

**Proof.** From the actual term $C$, the two legal addressed words
$P_R S_R$ and $S_L P_R$ reach $A_0$ and $A_1$, respectively. In the
first word, $P_R$ supplies precisely the beta guard for $S_R$; in the
second, $S_L$ uses the left beta and leaves the right alpha available
for $P_R$. From $A_0$ the event $S_L$, and from $A_1$ the event $S_R$,
reach the identical $D$. All statements concern actual edits, with
beta on the left at every split.

AA17.2 excludes $\langle\alpha,\beta\rangle$ from the native fibre of
$U(C)$, so $C$ is its unique representative. The two child classes
beta and $C$ can occur in either order, giving exactly $A_0,A_1$ over
$U(A_0)$. At a pair of equal child classes, the native ordered fibre
is the Cartesian square of the child fibre, as in (IV.64), without an
additional exchange factor. Thus $U(B_k(A_0))$ has exactly
$2^{2^k}$ native ordered representatives, obtained by independently
putting $A_0$ or $A_1$ at its $2^k$ bottom addresses. The same recursion
makes $B_k(C)$ and $B_k(D)=B_{k+1}(C)$ singleton orientation fibres.

Starting after the specified $h$, perform one of the two displayed
words in each disjoint bottom $C$ block, in a fixed block order. Prefix
each local address by its block address. No event touches another
block, so all guards remain valid at every intermediate prefix.
This realizes all $2^{2^k}$ distinct ordered intermediate terms with
the same $U$. Their complete $J$ values must be distinct by (IV.70),
and all extend the one fixed word $J(h)$. There are only
$\sum_{j=0}^{r-1}2^j=2^r-1$ binary suffixes of length less than $r$.
With $r=2^k$, at least one intermediate continuation therefore adds
at least $2^k$ bits. Complete its blocks by the respective single
splits above. Literal prefix preservation retains the length gained,
even if different records subsequently coincide.

The initial $C$ is reached by $P_\varepsilon S_\varepsilon$. Apply
the every-prefix conclusion successively for $k=0,\ldots,n-1$;
$\sum_{k<n}2^k=2^n-1$. The leaf counts at $B_n(C)$ are
$a=c=2^n$, proving its grade. A fresh static recoding at this endpoint
needs zero orientation bits, yet a coherent recorder retains the
mandatory accumulated length. This is a length claim along a selected
history, not a claim that every history is long or that its earlier
cuts remain distinguishable. $\square$

## 28. Uniform native successors in the balanced promotion family

**Definition 28.1 (balanced colours).** For $0\le k\le2^d$ define

$$
Q_0(0)=C,\qquad Q_0(1)=\langle\beta,\beta\rangle,
\qquad
Q_d(k)=\left\langle
Q_{d-1}(\lfloor k/2\rfloor),
Q_{d-1}(\lceil k/2\rceil)\right\rangle\quad(d\ge1).
\tag{IV.73}
$$

Put $m=2^d$, $U_{d,k}=U(Q_d(k))$, and let $\operatorname{pop}(k)$
be the number of ones in the binary expansion of $k$.

**Theorem 28.2 (exact outgoing multiplicity at every representative).**
All $Q_d(k)$ are native reachable. For every $0\le k<m$ and every
reachable ordered representative $t$ of $U_{d,k}$, exactly

$$
q_d(k)=2^{d-\operatorname{pop}(k)}
\tag{IV.74}
$$

actual alpha-leaf promotions $P_p$ have next quotient $U_{d,k+1}$.
Their ordered outputs are pairwise distinct. No other successful event
has that next quotient. Moreover

$$
a(Q_d(k))=m-k,\qquad c(Q_d(k))=m+k,\qquad
N(Q_d(k))=3m+k-1.
\tag{IV.75}
$$

Both $U_{d,0}$ and $U_{d,m}$ have singleton native orientation fibres;
the latter's unique term is the all-beta perfect tree $Q_d(m)$.

**Proof.** Every alpha leaf is the right leaf of a bottom $C$ cherry.
There is no alpha at an $L$-ending address. AA17.2 therefore gives
native realizability: from the prescribed birth type, promote an
alpha-born root if its target is non-alpha, split if the target is a
branch, and recursively build its beta-born left and alpha-born right
children. These steps have their actual guards and use no graft or
unrestricted orientation operation. Counting bottom cherries gives
(IV.75). At $k=0$ every bottom cherry has the forced ordering $C$,
and all higher children are recursively equal; at $k=m$ every leaf
is beta and all children are recursively equal. This proves both
singleton claims on the native domain.

For the uniform count induct on $d$, simultaneously over every
representative. At $d=0,k=0$, the unique term is $C$ and precisely
$P_R$ qualifies, giving $q_0(0)=1$. At a higher level write
$n=2^{d-1}$. A child of class $U_{d-1,r}$ has $n-r$ alpha leaves,
so different $r$ give different classes. Each current child is a
reachable representative of its prescribed class: the native leaf
condition restricts to it, and these child roots are non-alpha.
Consequently the induction applies in either actual child order.

If $k=2r$, both child classes are $U_{d-1,r}$ and the required next
multiset is $\{U_{d-1,r},U_{d-1,r+1}\}$. A qualifying promotion can
occur in either child, with exactly the inductively counted choices
in that child. If $k=2r+1$, the current child classes are $r,r+1$ in
either order and the required next classes are $r+1,r+1$. Only the
child with class $r$ can change. Promoting in the other child leaves
an unchanged class $r$, which has the wrong alpha count. Within the
class-$r$ child the promotion must be exactly an inductively
qualifying one. Hence, uniformly in the representative,

$$
q_d(2r)=2q_{d-1}(r),\qquad
q_d(2r+1)=q_{d-1}(r).
\tag{IV.76}
$$

The binary popcount identities prove (IV.74). Different selected
addresses are distinct alpha leaves; after promoting one, another
still contains alpha, so the ordered outputs differ. Equal-child
automorphisms identify their unordered observations, not these
ordered outputs, and introduce no division or extra multiplicity.
All these $P$ guards are actual alpha guards. Every $S$ increases
the leaf count, whereas $U_{d,k+1}$ has the same leaf count as
$U_{d,k}$, excluding every split. The count is outgoing from a fixed
current representative. It is not a count of predecessors of the
next quotient, nor of unrestricted orientations. $\square$

**Theorem 28.3 (accumulation on one selected history to a singleton).**
For every recorder (27.1), every $d\ge0$, and every fixed legal prefix
$h_0$ ending at $Q_d(0)$, there is a continuation $v$ of exactly $m$
actual promotions such that

$$
t(h_0v)=Q_d(m),\qquad
|J(h_0v)|-|J(h_0)|\ge\frac{dm}{2},\qquad
N(Q_d(m))=4m-1.
\tag{IV.77}
$$

In particular the maximum over histories at this recorder-independent
singleton orientation endpoint is at least
$\frac m2\log_2m$. The assertion selects a history for each recorder;
it does not impose this length on every history.

**Proof.** Suppose the already selected prefix $h_k$ has quotient
$U_{d,k}$ and put $\ell_k=d-\operatorname{pop}(k)$. Theorem 28.2
supplies $2^{\ell_k}$ legal successors with the same next quotient
and distinct ordered answers. Their $J$ words must be distinct and
extend the one word $J(h_k)$. If $\ell_k>0$, the same finite-word
count used in Theorem 27.2 forces one successor suffix to have length
at least $\ell_k$; for $\ell_k=0$ prefix preservation suffices.
Choose that successor as $h_{k+1}$. Uniformity over **every** current
representative permits this choice for each $k<m$, without discarding
the previously accumulated prefix. All selected histories are nested.

For $d\ge1$, each of the $d$ binary positions occurs in exactly $m/2$
of $0,\ldots,m-1$. Thus

$$
\sum_{k=0}^{m-1}\ell_k
=dm-\sum_{k=0}^{m-1}\operatorname{pop}(k)=\frac{dm}{2}.
\tag{IV.78}
$$

The final singleton in Theorem 28.2 forces the same $Q_d(m)$,
independently of the recorder and all selected choices. Its grade is
(IV.75). For $d=0$ there is just $P_R:C\to\langle\beta,\beta\rangle$;
the bound is zero. This endpoint has the unique full history
$P_\varepsilon S_\varepsilon P_R$. For $d\ge1$, terminal histories
need not be unique: the last promotions of two different bottom
cherries can be interchanged. Singleton orientation is not singleton
chronology.

For example, at $d=1$, $\langle C,C\rangle$ has promotions $P_{LR}$
and $P_{RR}$ to the different ordered terms
$\langle Q_0(1),C\rangle$ and $\langle C,Q_0(1)\rangle$ with equal
quotient. Promoting the remaining alpha in either reaches the same
$\langle Q_0(1),Q_0(1)\rangle$. At least one first choice adds a bit;
reconvergence cannot shorten that selected word. Records on different
histories may later coincide, so no history recovery is inferred.
$\square$

## 29. Exact-grade padding and the existing ordinal upper

**Corollary 29.1 (legal padding to every sufficiently large grade).**
For each integer $N\ge7$, choose the largest power of two
$m=2^d\le(N+1)/4$, and put $r=N-(4m-1)$. Every recorder has a legal
history of exactly $N$ events whose retained length is at least

$$
\frac{dm}{2}=\frac m2\log_2m
\ge\frac{N+1}{16}\log_2\frac{N+1}{8}.
\tag{IV.79}
$$

The padded endpoint can be chosen independently of the recorder;
no singleton orientation claim is made for it when $r>0$.

**Proof.** First use Theorem 28.3. The leftmost leaf of $Q_d(m)$ is
beta at $L^{d+1}$. Append the fixed sequence of splits at
$L^{d+1},L^{d+2},\ldots,L^{d+r}$, empty for $r=0$.
Each split creates the next left beta operand, so these are exactly
$r$ legal events and leave a fixed endpoint. Prefix preservation
retains the bound already obtained. Maximality of $m$ gives
$m>(N+1)/8$; for $N\ge7$ the logarithms compared in (IV.79) are
nonnegative, proving the stated weakening. $\square$

**Theorem 29.2 (U-input adapter and asymptotic minimax payload).**
AAII Definition 94.1's existing ordinal journal is a recorder under
(27.1), with a computable update from precisely $(U,J,e)$ and paid
transient scratch. If $\mathscr R_{\rm sem}$ denotes all semantic
recorders (27.1) and $\mathscr R_{\rm comp}$ those with computable
decoding and such an update, define

$$
M_{\mathscr R}(N)=\inf_{R\in\mathscr R}\;
 \max_{h:\,|h|=N}|J_R(h)|.
\tag{IV.80}
$$

For $N\ge7$, both classes satisfy

$$
\frac{N+1}{16}\log_2\frac{N+1}{8}
\le M_{\mathscr R_{\rm sem}}(N)
\le M_{\mathscr R_{\rm comp}}(N)
\le\sum_{j=1}^{N-1}\lceil\log_2j\rceil,
\qquad M_{\mathscr R}(N)=\Theta(N\log N).
\tag{IV.81}
$$

This is the asymptotic minimax retained binary-payload order, without
a sharp leading constant or a total-resource optimum.

**Proof.** Reuse the ordinal journal unchanged: before each actual
event, append the zero-based left-to-right rank of its operand among
the $L$ logical leaves, in exactly $\lceil\log_2L\rceil$ padded bits.
There are no kind bits, per-event markers or retained widths, and a
one-leaf event appends the empty word. No new sufficient code is needed.

The adapter's first step is justified by the admitted input itself:
$U$ retains leaf colours, hence supplies $a,c$ and the exact event
count $N=a+2c-1$. AAII94's inverse uses its current endpoint only to
obtain that count. Start in scratch at the known alpha, and run its
replay for exactly $N$ iterations. At each iteration the recovered
ordered scratch tree supplies $L$, the chunk width, the leaf at the
next chunk's rank, and that leaf's sole enabled kind and logical
address. The induction of AAII Theorem 94.2 therefore applies with
$U$ in place of an ordered-source input: the scratch tree after each
iteration is the actual historical term. At the end it is the
required current ordered term, and exactly all of $J$ has been
consumed. Zero-width events still advance the replay count.

For update, reconstruct that current term from $(U,J)$, locate the
supplied actual event $e=(\text{kind},p)$ in it, and compute its
pre-edit leaf rank and $L$ in scratch. Append exactly the same padded
ordinal bits. Its kind agrees with the leaf's actual guard. This
computes the next $J$ using only the admitted inputs, with literal
prefix preservation for every legal history. Replay trees, counters,
leaf scans, the event and append workspace are paid transient data;
none is retained as controller advice. The current ordered term is
computed, not supplied as an additional input. AAII Proposition 94.3
then gives the upper in (IV.81), with maximum zero at $N=0$ and
$\sum_{j=1}^{N-1}\lceil\log_2j\rceil$ at $N\ge1$.

Corollary 29.1 applies to every semantic recorder, and the effective
class is a subclass. These facts prove the inequalities. The lower
is $\Omega(N\log N)$ and the supplied upper is $O(N\log N)$.
Although this sufficient journal also replays history, history
recovery is not a premise of the lower bound or the minimax task.
$\square$

**Definition 29.3 (resource and supplier boundary).** The claim concerns
only retained binary content under the declared $U$ input. Finite
replay and rank computation may consume paid time, arithmetic,
transient backing and retained cleared capacity. Physical acquisition
of $U$, genuine operand bindings, rights, source edits, acknowledgements
and return to Ready remain separate AA20 premises; a symbolic address
does not grant them. Neither reset retention nor a callable service
is established by this adapter. The original services and the
full-history tasks keep their own interfaces and resource accounts.

AA17/19 supply the native guards, realizability and event counts;
§§23–26 supply the exact native quotient; AAII94 supplies the journal,
replay induction and upper. GPO22–23's global-substitution originals
have a different domain. The existing
[ImmutableExtension](../../../D5/S0/Computability/Coding/ImmutableExtension.lean)
and its [owning Scribe](../../../Blueprint/D5/S0/Computability/Coding/ImmutableExtension.scribe.cs)
require prefix-incomparable code extensions.
[MinimumRollbackAlphabet](../../../D5/S0/History/Coding/MinimumRollbackAlphabet.lean)
and its [Scribe](../../../Blueprint/D5/S0/History/Coding/MinimumRollbackAlphabet.scribe.cs)
concern static injective fibre labels.
[AppendOnlyAnswerabilityMonotonicity](../../../D5/S3/ConceptDynamics/History/AppendOnlyAnswerabilityMonotonicity.lean)
and its [Scribe](../../../Blueprint/D5/S3/ConceptDynamics/History/AppendOnlyAnswerabilityMonotonicity.scribe.cs)
assume an old-log projection, which literal word extension without the
old cut's length does not supply.
[StateRecordReadoutDistinguishability](../../../D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.lean)
and its [Scribe](../../../Blueprint/D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.scribe.cs)
give conditional separation of certified record readouts, not these
quantitative native bounds. None of those premises is silently added
to (IV.70).

Finite-word counting, online adversaries, ranking and rooted-tree
symmetry are classical suppliers. Relevant comparisons are Cover,
[*Enumerative Source Encoding*, §§I–II](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf),
for ranking; Bennett,
[*Logical Reversibility of Computation*](https://doi.org/10.1147/rd.176.0525),
for history and replay; Rivest–Shamir,
*How to Reuse a Write-Once Memory*, §§I–II,
whose fixed-cell coordinatewise write order differs from literal word
prefix; and Kersting–Fischer,
[*Measuring tree balance using symmetry nodes*, §2 and Lemma 3.2](https://arxiv.org/pdf/2105.00719v2),
for rooted symmetry. The source-specific contribution is the uniform
actual native transition/retention bridge and the explicit weaker-input
adapter, not those general methods. This source-relative synthesis
makes no exhaustive novelty claim; these are ordinary mathematical
arguments, not Lean validation.

## 追加锚（本行以下为增补区）

## 30. Paid tail editing for current-term recovery

**Definition 30.1 (settled record and actual edit resources).** Retain
Definition 23.1's known initial alpha and **every** finite legal history
of the actual addressed operations
$P_p:\alpha\to\beta$ and
$S_p:\beta\to\langle\beta,\alpha\rangle$, with beta on the left.
Only the record interface changes. A deterministic recorder $R$ starts
with $J_R(\varepsilon)=\varepsilon$. After an actual enabled event $e$
it transforms $J_R(h)$ to $J_R(he)$ by a finite sequence of unit-cost
operations: POP deletes the last bit of a nonempty word, and
APPEND$(b)$ appends one bit $b\in\{0,1\}$. It must satisfy, at every
settled cut,

$$
\operatorname{Dec}_R(U(t(h)),J_R(h))=t(h).
\tag{IV.82}
$$

The whole finite word and its end are visible. Intermediate words need
not decode. Fixed code is common to all histories. Update uses only
$(U(t(h)),J_R(h),e)$, with finite separately paid transient scratch
cleared before the next settled cut. There is no other retained variable
channel: no controller register, event counter, old output, address
roster, allocation chronology, archived word, or advice available to
update or decoding. In particular scratch capacity cannot encode usable
advice between cuts. The observation $U$ is the same unordered coloured
rooted input as before, not a newly acquired physical port. Its leaf
counts supply the grade $n=a+2c-1=|h|$ by Proposition 23.2.

Let $c_R(h,e)$ be the number of **actual** POPs and APPENDs in this
update, including any detours. For $h=e_1\cdots e_N$ put

$$
T_R(h)=\sum_{i=1}^N c_R(e_1\cdots e_{i-1},e_i),\qquad
T_R^{\max}(N)=\max_{|h|=N}T_R(h).
\tag{IV.83}
$$

Let $p_R(h)$ be the maximum record length at any settled cut or
intermediate record edit along $h$, including the initial empty word,
and put $P_R^{\max}(N)=\max_{|h|=N}p_R(h)$. These maxima exist: at a
fixed grade there are finitely many legal addressed histories, each with
finitely many record edits. Scratch, source access, source edits,
arithmetic, execution time and cleared allocated capacity are separately
paid; neither (IV.83) nor $p_R$ measures their total cost. No old-cut or
full-history inverse is required. The literal-prefix contract (IV.70)
and all earlier full-history problems retain their own definitions.

**Theorem 30.2 (balanced promotion forces cumulative actual edits).**
For every admissible deterministic recorder $R$, every integer $d\ge0$,
$m=2^d$, and every legal prefix $h_0$ ending at $Q_d(0)$, some legal
continuation $v$ of exactly $m$ actual promotions ends at $Q_d(m)$ and
satisfies

$$
T_R(h_0v)-T_R(h_0)\ge \Lambda_d,
\qquad \Lambda_d=\frac{dm}{2}-m+1.
\tag{IV.84}
$$

Here $\Lambda_0=\Lambda_1=0$; strict growth is an asymptotic conclusion, not a claim
at those two depths. For every $R$ and every integer $N\ge63$, there is
a legal history of **exactly** $N$ events with

$$
T_R(h)\ge\frac{N+1}{32}\log_2\frac{N+1}{8}.
\tag{IV.85}
$$

Thus $T_R^{\max}(N)=\Omega(N\log N)$ uniformly over recorders, even
though a paid POP can shorten the retained word.

**Proof.** The graph of finite binary words, with an edge from $x$ to
$x0$ and $x1$, is a tree of maximum degree three. Its graph distance is

$$
\delta(x,y)=|x|+|y|-2|\operatorname{lcp}(x,y)|.
\tag{IV.86}
$$

Indeed every route must first delete to the longest common prefix and
then reach the other word; that route attains the displayed length.
Consequently every actual editing sequence costs at least $\delta$.
For integer $r\ge0$ a distance ball about any word contains at most

$$
1+\sum_{i=1}^r3\cdot2^{i-1}=3\cdot2^r-2
\tag{IV.87}
$$

words: at most three first edges and at most two forward edges at each
subsequent shell. This is the usual finite-degree metric counting
argument; no prefix-free coding premise is involved.

Suppose a selected prefix $h_k$ has quotient $U_{d,k}$, with $k<m$,
and write $\ell_k=d-\operatorname{pop}(k)$. Theorem 28.2 applies to
**every** current ordered representative, not only to $Q_d(k)$. It gives
$2^{\ell_k}$ actual enabled promotions with distinct ordered outputs and
the same next quotient $U_{d,k+1}$. Their settled record words are
pairwise distinct by (IV.82). If $\ell_k\ge2$, the ball of radius
$\ell_k-2$ about the one current word contains at most
$3\cdot2^{\ell_k-2}-2<2^{\ell_k}$ words. Some successor therefore has
distance at least $\ell_k-1$, and its actual update costs at least that
much. If $\ell_k=1$ or $0$, nonnegativity supplies the weaker bound
$\max(\ell_k-1,0)$. Select a successor satisfying this bound and repeat.
The uniform outgoing lemma permits all $m$ choices on one nested
history, with no change of the previously selected prefix.

Only $k=m-1$ has $\ell_k=0$. For $d\ge1$, the popcount sum (IV.78)
therefore gives

$$
\sum_{k=0}^{m-1}\max(\ell_k-1,0)
=\sum_{k=0}^{m-1}\ell_k-(m-1)
=\frac{dm}{2}-m+1.
\tag{IV.88}
$$

For $d=0$ the sum and the displayed expression are both zero. At the
end Theorem 28.2 forces the common ordered term $Q_d(m)$, whose grade
is $4m-1$. Additivity of actual edit counts proves (IV.84). It does not
assert that the final record has length $\Lambda_d$; erasure can remove it.

For a prescribed $N\ge63$, take the largest power of two
$m=2^d\le(N+1)/4$. Reach $Q_d(0)$ by any legal prefix and then use
(IV.84). Here $d\ge4$, so $\Lambda_d\ge dm/4$, and
$m>(N+1)/8$. If $r=N-(4m-1)$ is positive, append the $r$ actual splits
at $L^{d+1},L^{d+2},\ldots,L^{d+r}$, as in Corollary 29.1. The first
operand is beta in $Q_d(m)$ and each split creates the next left beta,
so this is legal padding to exactly $N$. Cumulative cost cannot decrease
under padding, regardless of subsequent POPs. Comparing the nonnegative
logarithms yields (IV.85). The selected promotion history may depend on
$R$; the unpadded terminal term does not. $\square$

## 31. A uniform recorder with linear peak payload

**Definition 31.1 (grade-determined snapshot blocks).** Reuse the
constructor serialization of
[AAII Definition 54.1](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#54-a-destructive-probe-acquires-both-the-entry-and-its-real-endpoint):
$\sigma(\alpha)=00$, $\sigma(\beta)=01$, and
$\sigma(\langle v,w\rangle)=10\sigma(v)\sigma(w)$.
The tags are parsed in preorder. One pending subtree slot is replaced
by two at a branch and filled at a leaf, so the first return to zero
pending slots uniquely ends the serialized tree. A tree with $L$ leaves
has $2L-1$ vertices. In particular a grade-$b$ native term has

$$
|\sigma(t)|=4L-2\le4b+2,
\tag{IV.89}
$$

since each split adds one leaf and hence $L\le b+1$. These serialization
and parsing facts are existing suppliers, not additional claims of
coding novelty.

For each integer $j\ge0$, put

$$
M_j=2^j,\qquad \Delta_j=\max\left(1,
\left\lfloor\frac{2^j}{j+1}\right\rfloor\right),\qquad
\mathcal S_j=\{M_j+q\Delta_j:q\ge0,\ M_j+q\Delta_j<2M_j\}.
\tag{IV.90}
$$

The positive snapshot grades are $\mathcal S=\bigcup_{j\ge0}\mathcal S_j$.
For $n\ge1$, $b(n)$ is the largest snapshot grade at most $n$; set
$b(0)=0$. All these quantities are computed from the current grade,
without a retained schedule index or a supplied horizon.

At grade $n\ge1$ the maintained word consists of
$\sigma(t(h_{b(n)}))$ followed by the AAII94 ordinal chunks for just
the events after that prefix. Here $h_i$ denotes the length-$i$ prefix
of the actual history. Precisely,

$$
J_*(h)=\sigma(t(h_{b(n)}))
\prod_{i=b(n)+1}^{n}\operatorname{bin}_{w_i}(r_i),
\qquad w_i=\lceil\log_2L_i\rceil,
\quad J_*(\varepsilon)=\varepsilon,
\tag{IV.91}
$$

where concatenation is chronological, and $r_i,L_i$ are the actual
pre-event logical leaf rank and leaf count of AAII Definition 94.1.
There is no stored block header, width, event kind or historical cut
marker. The empty initial word is treated separately at grade zero.

**Theorem 31.2 (computable attainment on all histories).** There is one
computable, horizon-independent recorder $R_*$ realizing (IV.91), with
update from exactly $(U,J,e)$ and cleared finite paid scratch, such that
(IV.82) holds for every legal finite history. There are absolute
constants $C_T,C_P$ such that, for every integer $N\ge1$ and every
legal history $h$ of exactly $N$ events,

$$
T_*(h)\le C_T N\log_2(N+2),\qquad p_*(h)\le C_P N.
\tag{IV.92}
$$

The peak includes every intermediate word during snapshot rewriting.
The assertion bounds cumulative edits, not the maximum individual
update by $O(\log N)$.

**Proof.** Given $(U,J)$ at a settled cut, first compute $n=a+2c-1$.
If $n=0$, return the known alpha from the empty word. Otherwise compute
$b=b(n)$ and parse the first complete $\sigma$ tree from the head of
$J$. On the actual image this is precisely the grade-$b$ snapshot in
(IV.91); parsing supplies its end without an extra delimiter. Starting
from that ordered tree in scratch, replay exactly $n-b$ ordinal chunks.
At each iteration the scratch tree determines its ordered logical leaves,
$L_i$, the width $w_i$, and the leaf of the encoded rank. That leaf has
exactly one enabled kind, $P$ at alpha and $S$ at beta, and its ordered
position gives the address. Apply that edit in scratch. The induction in
[AAII Theorem 94.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#94-a-raw-ordinal-stream-and-its-source-conditioned-inverse)
uses only equality of the starting scratch tree and the actual starting
tree. With the snapshot as its base, it therefore recovers each actual
subsequent tree and consumes exactly the suffix in (IV.91). Zero-width
iterations still advance the known replay count. It ends at the actual
current term, proving (IV.82). In particular this use of replay does not
assume an ordered current-source input: $U$ supplies only the stopping
grade, just as in the adapter of Theorem 29.2.

For update, decode the old ordered term from $(U,J)$ in scratch and
locate the supplied actual event $e=(\mathrm{kind},p)$. Its guard is
satisfied because it is an actual enabled event. Compute its pre-event
rank, width and new term in scratch. If $n+1\notin\mathcal S$, append
exactly its padded ordinal chunk. Then $b(n+1)=b(n)$, so (IV.91) is
preserved. If $n+1\in\mathcal S$, prepare $\sigma(t(he))$ in scratch,
POP every bit of the old word, and APPEND every bit of that serialization
in order. The new word is the snapshot with empty suffix required by
$b(n+1)=n+1$. Every POP and APPEND is charged; neither deletion of the
old snapshot nor copying of the new one is free. This includes the first
event: grade one is a snapshot grade and its word is $\sigma(\beta)$.
The actual source event is supplied, not selected by the recorder.

The input tree and word are finite. Parsing, addressed lookup,
simulation, rank calculation, schedule arithmetic, and each finite replay
therefore terminate with finite backing. The prepared snapshot and all
replay trees, cursors, ranks, counters, event data and schedule data are
transient paid scratch, cleared before the next settled cut. During the
busy update only scratch supports the finite discrepancy; intermediate
records need not satisfy (IV.82). No earlier snapshot is retained
elsewhere after rewriting. Thus neither the construction nor its inverse
uses a hidden persistent clock, tree copy or auxiliary advice.

For the resource bounds fix a current grade $M=2^j\le n<2M$.
Its last snapshot grade $b$ is in this same epoch, and $0\le n-b<\Delta_j$.
Before event $i\le n$ the leaf count is at most $i\le n<2^{j+1}$,
so each chunk has at most $j+1$ bits. Hence

$$
|J_*(h)|\le4b+2+(\Delta_j-1)(j+1)
\le8M+2+M\le11n.
\tag{IV.93}
$$

At a snapshot rewrite, the record first decreases to empty and then
grows to the new serialization. Its length never exceeds the larger of
the old and new settled lengths. A non-snapshot append is monotone in
length. Applying (IV.93) also to earlier settled grades proves
$p_*(h)\le11N$, including the initial word and all busy intermediates.
An output buffer in scratch is separately paid, not an extra uncounted
record channel at a settled cut.

There are exactly $M$ new event grades in $[M,2M)$. The non-snapshot
appends there cost at most $M(j+1)$ altogether. Since $2^j\ge j+1$,
$\Delta_j\ge M/(2(j+1))$, and the number of snapshot grades is
$\lceil M/\Delta_j\rceil\le2(j+1)+1$. At a snapshot grade $s$ the actual
rewrite costs

$$
|J_*(h_{s-1})|+|\sigma(t(h_s))|
\le11(s-1)+4s+2\le17s<34M.
\tag{IV.94}
$$

Thus the entire epoch, or any partial epoch starting at $M$, costs at
most a fixed constant times $M(j+1)$. If $2^K\le N<2^{K+1}$,

$$
\sum_{j=0}^K 2^j(j+1)
\le(K+1)(2^{K+1}-1)\le2N(K+1)
=O(N\log_2(N+2)).
\tag{IV.95}
$$

This proves (IV.92) with constants independent of $N$, the history and
any future horizon. It proves no bound on all separately paid resources.
$\square$

## 32. Optimal orders and the chronology boundary

**Theorem 32.1 (linear necessary peak and joint attainment of orders).**
For every admissible deterministic recorder $R$ and every integer
$N\ge4$,

$$
P_R^{\max}(N)\ge m_N>\frac{N+1}{10},\qquad
m_N=\max\{2^k:5\cdot2^k-1\le N\}.
\tag{IV.96}
$$

Together with Theorems 30.2 and 31.2, this says explicitly

$$
\begin{aligned}
&\exists c_T,c_P>0\ \exists N_0\ \forall R\ \forall N\ge N_0:\quad
T_R^{\max}(N)\ge c_TN\log_2N,\quad P_R^{\max}(N)\ge c_PN,\\
&\exists\text{ one computable }R_*\ \exists C_T,C_P>0\
\forall N\ge1\ \forall h\ (|h|=N):\quad
T_*(h)\le C_TN\log_2(N+2),\quad p_*(h)\le C_PN.
\end{aligned}
\tag{IV.97}
$$

Thus the same recorder attains the optimal asymptotic orders in the two
coordinates. The two maxima in the first line are separate: their
witness histories need not coincide.

**Proof.** Use $A_0,A_1$ and $B_k$ from (IV.71), with $m=2^k$.
The existing current-orientation count (IV.64), as applied in Theorem
27.2, gives exactly $2^m$ reachable ordered terms over
$U(B_k(A_0))$, independently choosing $A_0$ or $A_1$ at each bottom
block. They have $a=m,c=2m$, hence all have grade $5m-1$. Choose one
legal history for each ordered term. By (IV.82) their settled record
words must be distinct. Words of lengths zero through $m-1$ number
only $2^m-1$. At least one of these histories therefore has a settled
record of length at least $m$, without any prefix-free assumption.

Take $m=m_N$. Extend that witnessing history by exactly
$N-(5m-1)$ further events, if needed, by repeatedly splitting its current
leftmost beta leaf. Such a leaf exists and every split creates the next
left beta, so any required finite extension is legal. The earlier
length-$m$ word remains in the **peak** even if later updates erase it.
Maximality of the power of two gives $2m>(N+1)/5$, proving (IV.96).
The lower uses the orientation fibre, not the much larger full-history
fibre. Apply (IV.85) for the other coordinate and (IV.92) for the one
common upper recorder to obtain (IV.97). This compares orders of these
two worst-case resources; it supplies no sharp constants, full Pareto
frontier or total-resource optimum. $\square$

**Proposition 32.2 (current recovery can discard full native history).**
The recorder $R_*$ need not determine the full addressed history from
$(U,J_*)$. There are two distinct legal histories of grade seven with
the same ordered endpoint and the same $J_*$. In contrast $Q_0(1)$ has
a unique full history.

**Proof.** Start with the legal five-event prefix

$$
h_0=P_\varepsilon S_\varepsilon S_L P_R S_R.
\tag{IV.98}
$$

Its successive terms are $\alpha$, $\beta$, $C$,
$\langle C,\alpha\rangle$, $\langle C,\beta\rangle$, and
$\langle C,C\rangle$. Thus all guards use the actual beta-left native
rules. The two continuations $P_{LR}P_{RR}$ and $P_{RR}P_{LR}$ promote
the two different right alpha leaves in opposite orders, reaching in
both cases
$\langle\langle\beta,\beta\rangle,\langle\beta,\beta\rangle\rangle
=Q_1(2)$. They are distinct addressed histories. Grade seven belongs to
$\mathcal S_2$, since $M_2=4$ and $\Delta_2=1$. At that cut (IV.91) is
just the serialization of the common current term, with no journal
suffix. The pair $(U,J_*)$ is therefore identical for these histories,
so it cannot recover their different chronologies. On the other hand,
the only history of $Q_0(1)=\langle\beta,\beta\rangle$ is
$P_\varepsilon S_\varepsilon P_R$, as also checked in Theorem 28.3.
Consequently a singleton ordered endpoint must not be described as
having nonunique histories without an additional native instance.
$\square$

## 33. Suppliers and the extent of the paid-tail conclusion

**Definition 33.1 (source correspondence and literature scope).**
The native domain, source-derived grade and orientation fibres are
[AA17/19](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md)
and §§23–26; Theorem 28.2 is the uniform outgoing balanced-promotion
supplier used in (IV.84). The literal-prefix accumulation of Theorem
28.3 is not a paid-tail lower bound: (IV.86)–(IV.88) replace that step.
AAII Definition 54.1 supplies constructor serialization; AAII Definition
94.1 and Theorem 94.2 supply the ordinal journal and replay induction,
with Theorem 29.2's weaker $U$-input correspondence. Here their replay
base is an explicitly retained current-term snapshot, so histories before
that base are not reconstructed.

Finite-degree ball counting, finite-word capacity, serialization,
finite-set ranking, and balancing snapshot cost against short journals
are general methods. Cover,
[*Enumerative Source Encoding*, §§I–II, Proposition 1 and its inverse](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf),
supplies the classical ranking perspective already used for the static
fibres. The recorder (IV.91) uses the existing constructor and ordinal
serializations rather than claiming a new enumerative coding theorem.

Varshney–Kusuma–Goyal,
[*Malleable Coding: Compressed Palimpsests*, §§IV, VI–VII](https://arxiv.org/abs/0806.4722v1),
formulate correlated random blocks and costs in a codeword edit metric;
their general metric formulation and coding results are relevant prior
work. Their
[*Malleable Coding with Fixed Reuse*, §III and Theorem 1](https://arxiv.org/abs/0809.0737v2),
uses independent drawings of correlated symbol pairs, block codes with
vanishing error, and a fixed reused prefix portion. Neither stochastic
block contract supplies the exact deterministic all-history native
quantifiers, the uniform actual addressed successors, or the grade-based
snapshot/replay construction in (IV.97). Conversely (IV.97) makes no
claim about their stochastic rate regions. The additional deduction is
the source-specific uniform synthesis under (IV.82), not the general
coding suppliers or an exhaustive originality claim.

The result concerns present ordered contents, cumulative actual tail
edits, and maximum retained word length, with all busy word lengths
counted. It neither strengthens the original append-only record contract
nor solves a full-history task. Actual physical acquisition of $U$,
source-bound operand authority, acknowledgements and return, separately
paid computation and work backing retain their original premises. In
particular a mathematical address supplies no new physical port. The
exact all-$k$ worst-individual-update question remains unresolved here:
the amortized estimate (IV.95) is not an every-step logarithmic bound.
No sharp constants, complete Pareto frontier, total resource optimality
or Lean verification is asserted by these ordinary arguments.

## 追加锚（本行以下为增补区）

## 34. All-history labelled bits with paid tail updates

**Definition 34.1 (the causal record contract).** Fix an integer $k\ge1$.
An input history is any sequence $h=((j_1,b_1),\ldots,(j_m,b_m))$,
$0\le m\le k$, of distinct labels $j_i\in[k]$ and arbitrary bits
$b_i\in\{0,1\}$. Write $A(h)=\{j_1,\ldots,j_m\}$ and
$x_h:A(h)\to\{0,1\}$ for its partial assignment. Every order and every
bit assignment is admitted. Fixed code and an arbitrary finite initial
word $K_0$ may depend on $k$, but are chosen before the unknown inputs.
At a settled cut the only variable retained record is one binary word
$K(h)$; the current subset $A(h)$ is supplied side information. Exactness
means, for every history and every allowed run,

$$
\operatorname{Dec}_k(A(h),K(h))=x_h.
\tag{IV.99}
$$

Update receives only $(k,A,K,j,b)$, with $j\notin A$, and produces the
next word by finitely many actual unit POPs and APPENDs, as in Definition
30.1. It is causal: a run on a prefix is independent of future labels
and bits. Deterministic update is allowed; if fresh internal choices are
allowed, every allowed outcome must terminate and satisfy (IV.99) and
the stated resource bounds. Such choices provide no additional retained
state. Computation, decoding, input handling and scratch are separately
paid, and scratch is cleared before return. No history, bits array,
controller, old word or advice is retained outside $(A,K)$. The whole
current word and its end are visible; there is no prefix-free or
history-injectivity requirement.

Let $c(h,j,b)$ count all actual tail edits, including detours, on the
particular run. A worst-update bound $D\in\mathbb N$ requires $c\le D$
on every insertion of every run. A true payload peak bound $L\in\mathbb N$
includes $K_0$, every settled word and every intermediate edit word.
Neither bound pays for scratch or total execution time. No canonical
record is required: for every partial assignment $x:A\to\{0,1\}$ use
**all** reachable settled words $R_{A,x}$ over all histories and allowed
outcomes with that assignment. With finite peak these sets are finite,
nonempty, and disjoint for different $x$ at the same $A$, by (IV.99).
In particular put $R_x=R_{[k],x}$ for terminal $x\in\{0,1\}^k$.

**Lemma 34.2 (edge-specific causal witnesses).** In this contract with
finite peak and worst-update bound $D$, every edge $xy$ of the Boolean
cube $Q_k$ has some $a\in R_x$, $b\in R_y$ at tail-tree distance at most
$2D$. The pair may depend on the edge.

**Proof.** If the edge differs at label $j$, insert the other $k-1$
labels first, in any one order with their shared bits, and choose one
allowed prefix run. Causality and future-independent $K_0$ give the same
prefix word $p$ before either choice of the last bit. Complete this run
with each last bit; the words $a,b$ obtained are in the respective
all-history terminal sets. Each actual edit path from $p$ has length at
most $D$, so the tree triangle inequality gives $d(a,b)\le2D$. A detour
cannot reduce its charged cost. No choice of one representative per
assignment has been used. $\square$

## 35. A separator counting fibres across one common cut

**Theorem 35.1 (original-branch separator).** Let $T$ be the tree of all
finite binary words, with edges $w\!-!wb$, $b\in\{0,1\}$, and unit
path metric $d$. The statement also holds for its truncation to lengths
at most any integer $L\ge0$, with balls and components taken there.
For every integer $k\ge1$, integer $D\ge0$, and family of finite,
nonempty, pairwise disjoint sets $(R_x)_{x\in\{0,1\}^k}$ of vertices of
$T$, assume

$$
\forall xy\in E(Q_k)\quad
\exists a_{xy}\in R_x\ \exists b_{xy}\in R_y:
\quad d(a_{xy},b_{xy})\le2D.
\tag{IV.100}
$$

Put $N=2^k$, $B_D(v)=\{w:d(w,v)\le D\}$, and define

$$
\begin{aligned}
C_v&=\#\{x:R_x\cap B_D(v)=\varnothing,\ R_x\text{ meets two components of }T-\{v\}\},\\
F_v&=\#\{x:R_x\cap B_D(v)=\varnothing,\ R_x\text{ meets two components of }T-B_D(v)\}.
\end{aligned}
\tag{IV.101}
$$

There exists one vertex $v$ such that

$$
F_v\ge C_v\ge
\max\!\left(0,\left\lceil\frac{N}{k+1}\right\rceil-|B_D(v)|\right)
\ge
\max\!\left(0,\left\lceil\frac{N}{k+1}\right\rceil-(3\cdot2^D-2)\right).
\tag{IV.102}
$$

Thus the same conclusion applies to Lemma 34.2's all-history sets,
without fixing edge endpoints globally or assuming fibre connectivity.

**Proof.** Choose one $r_x\in R_x$ **only for weights**, assigning one
unit of weight there. Their finite spanning subtree has a weighted
centroid $v$: every component of $T-\{v\}$ contains at most $N/2$
selected representatives. To prove this, start in that finite subtree
and move toward any component of weight greater than $N/2$. After a
move the reverse component has weight less than $N/2$, so it cannot be
the next heavy direction. A walk without reversal in a finite tree
cannot continue forever. At its last vertex no heavy component remains;
branches outside the finite subtree have weight zero. Disjointness
makes the selected representatives distinct. They need not be the
witnesses in (IV.100).

Let $I=\{x:R_x\cap B_D(v)\ne\varnothing\}$ and let $H$ be the set
counted by $C_v$. These classes are disjoint. Selecting a ball word for
each member of $I$ is injective, so $|I|\le|B_D(v)|$. Set $S=I\cup H$,
as a vertex set of $Q_k$. For every surviving $x\notin S$, the whole
nonempty $R_x$ lies in one original component of $T-\{v\}$, and all its
words have distance at least $D+1$ from $v$.

There is no cube edge between surviving fibres in different original
components. Indeed **every** pair $a,b$ across those components has its
unique tree path through $v$, hence

$$
d(a,b)=d(a,v)+d(v,b)\ge2D+2,
\tag{IV.103}
$$

contrary to the edge's own witnesses in (IV.100). Each connected
component $W$ of $Q_k-S$ therefore has all its representatives $r_x$
in one original branch at $v$, so $|W|\le N/2$ by centroid balance.

Here is a complete elementary expansion bound for the cube. For every
subset $W\subseteq V(Q_k)$ its edge boundary satisfies
$|\partial_E W|\ge\min(|W|,2^k-|W|)$. Induct from $Q_0$, where both
possible subsets have zero boundary. Split $Q_k$ into two $(k-1)$-cubes
of size $M=2^{k-1}$, and let their intersections with $W$ have sizes
$a,b$. Internal boundaries give at least
$\min(a,M-a)+\min(b,M-b)$ by induction. The matching between halves
adds at least $|a-b|$ crossing edges, since at most $\min(a,b)$ matched
pairs have both ends in $W$. Assume $a\ge b$. If $a,b\le M/2$, the
sum of these three bounds is $2a\ge a+b$. If $a,b\ge M/2$, it is
$2M-2b\ge2M-a-b$. In the remaining case $b\le M/2\le a$, it is
$M\ge\min(a+b,2M-a-b)$. This proves the induction in every case.

Apply this bound to each component $W$ of $Q_k-S$. Its size is at most
$N/2$, so $|\partial_E W|\ge|W|$; all its outgoing edges end in $S$.
Summing over the components counts each edge to $S$ once. Since every
cube vertex has degree $k$,

$$
N-|S|=\sum_W|W|\le\sum_W|\partial_E W|
=|E(S,V(Q_k)\setminus S)|\le k|S|.
\tag{IV.104}
$$

This includes the empty-complement case. Thus
$|S|\ge\lceil N/(k+1)\rceil$ and
$C_v=|S|-|I|\ge\lceil N/(k+1)\rceil-|B_D(v)|$.
A tree of maximum degree three has at most $3\cdot2^{i-1}$ vertices at
distance $i\ge1$ from a fixed vertex. Therefore
$|B_D(v)|\le1+3\sum_{i=0}^{D-1}2^i=3\cdot2^D-2$, also for $D=0$
with the empty sum. Root and truncation only reduce this count.
Every component of $T-B_D(v)$ lies in an original component of
$T-\{v\}$. Hence a fibre counted by $C_v$ is counted by $F_v$.
Nonnegativity completes (IV.102). $\square$

The original-branch qualification is essential. Different fine
components of $T-B_D(v)$ need not be more than $2D$ apart: for
$v=\varepsilon$, $D=1$, the words $00$ and $01$ are in different fine
components at distance two. Equation (IV.103) is used only across
original incident branches. Nor does the weighted choice assert a
fixed-representative embedding of the cube.

**Corollary 35.2 (connected fibres and logarithmic updates).** Under
Theorem 35.1's hypotheses, if every $R_x$ is connected in the word tree,
then

$$
3\cdot2^D-2\ge\left\lceil\frac{2^k}{k+1}\right\rceil,
\qquad
D\ge\max\!\left(0,\left\lceil\log_2
\frac{\lceil2^k/(k+1)\rceil+2}{3}\right\rceil\right).
\tag{IV.105}
$$

In particular $D\ge k-\log_2(12k)$. Without connectivity, for any fixed
real constants $c\ge0,c_0$, a family with integer
$D(k)\le c\log_2 k+c_0$ has one cut $v=v_k$ with

$$
C_v\ge\max\!\left(0,\left\lceil\frac{2^k}{k+1}\right\rceil
-3\cdot2^{c_0}k^c+2\right).
\tag{IV.106}
$$

For all sufficiently large $k$ this is at least $2^k/(2(k+1))$.
Each counted assignment has two record words in different original
branches, each outside the same ball, at distance at least $2D(k)+2$.

**Proof.** A connected vertex subset of a tree contains the unique path
between any two of its vertices. If it avoids $B_D(v)$, it therefore
lies in one component of the complement, so $F_v=C_v=0$. Equation
(IV.102), followed by rearrangement and integer rounding, proves
(IV.105). Dropping its positive additive term gives
$D\ge k-\log_2(3(k+1))\ge k-\log_2(12k)$. Substituting the assumed
upper bound on $D(k)$ into (IV.102) proves (IV.106); exponential growth
eventually exceeds twice the fixed polynomial loss. Equation (IV.103)
gives the separation of the two words. These are counts of assignments
across one common cut, not counts of histories, update events, word
vertices or all connected components. $\square$

## 36. The terminal-only boundary

**Proposition 36.1 (linear-length sets with distance-two contacts).**
For every $k\ge1$ there are disjoint nonempty terminal sets satisfying
(IV.100) with $D=1$, each of $k$ words of common length
$k+\lceil\log_2 k\rceil$. This statement supplies no causal updater.

**Proof.** The cube has $E=k2^{k-1}$ edges. Give each edge $e$ a
different binary prefix $p_e$ of length $m=\lceil\log_2 E\rceil$.
For an edge $e=xy$ differing at coordinate $j$, put $p_ex_j$ in $R_x$
and $p_ey_j$ in $R_y$. Every vertex has $k$ incident edges and therefore
$k$ distinct assigned leaves. A leaf's first $m$ bits identify its edge,
and its last bit distinguishes the two endpoints. No leaf belongs to
two fibres. The two leaves assigned to any edge have common prefix
$p_e$ and distance exactly two. Finally
$m+1=k+\lceil\log_2 k\rceil$. For $k\ge2$ each fibre consists of
multiple leaves with no joining path inside it, hence is disconnected.
No records for partial assignments, common initial word or compatible
extension rule have been constructed. Edge proximity is a necessary
relaxation of the causal contract, not its converse. $\square$

For comparison, the finite $k=3,L=3,D=1$ causal witness has 39 family
representatives but only 37 actually reachable state-word pairs; its
independent direct verifier covers 48 complete histories and 78 prefix
transitions. The disconnected $R_{\{2,3\},00}=\{01,11\}$ is a
**partial** fibre; the terminal example is $R_{000}=\{011,100,110\}$.
At these parameters (IV.102)'s uniform lower bound is zero. This finite
example supplies neither an all-$k$ scheme nor an asymptotic obstruction.
Its finite checks, like the ordinary proofs here, are not Lean verification.

## 37. The exact native alpha/beta connection

**Proposition 37.1 (prepared restriction and actual interfaces).** Use
AA17/19's native rules and Definition 30.1's current-term recorder.
For each $k\ge1$ the source-relative preparation bridge uses

$$
C=\langle\beta,\alpha\rangle,\quad
D_0=\langle\beta,C\rangle,\quad D_1=\langle C,\beta\rangle,\quad
M=\langle\langle C,\alpha\rangle,\alpha\rangle.
\tag{IV.107}
$$

The marker $M$ has **four** leaves. After a fixed preparation of
$g_0=3k+4$ events, any distinct-label insertion history is simulated
with exactly two actual native events per insertion. Its endpoint is
$F_1$, where $F_{k+1}=M$ and $F_j=\langle B_j,F_{j+1}\rangle$,
with $B_j=C$ if $j\notin A$ and $B_j=D_{x_j}$ otherwise. Its grade is
$3k+4+2|A|$, hence $5k+4$ at full assignment. The unordered coloured
quotient $U_{k,A}$ depends only on $k,A$ at these macro-cuts, while the
ordered endpoint determines all inserted labelled bits.

**Proof.** At $r=R^{j-1}$, for $j=1,\ldots,k$, the preparation executes
$P_r,S_r,S_{rL}$. It changes the current alpha continuation into
$\langle C,\alpha\rangle$ and proceeds into its right alpha. At
$r=R^k$ execute $P_r,S_r,S_{rL},S_{rLL}$, producing exactly the
bracketed four-leaf $M$ in (IV.107). Each promotion sees alpha and each
split sees beta. This accounts for $3k+4$ events. An inactive slot at
$q_j=R^{j-1}L$ is $C$. For insertion zero,
$P_{q_jR},S_{q_jR}$ changes it through
$\langle\beta,\beta\rangle$ to $D_0$; for insertion one,
$S_{q_jL},P_{q_jR}$ changes it through
$\langle C,\alpha\rangle$ to $D_1$. All guards hold, and different
slots are disjoint, so every insertion order is legal and the asserted
endpoint follows by induction.

Each slot has two or three leaves; every continuation has at least four.
Consequently even in the unordered quotient the continuation is the
unique larger child at each comb position. These positions identify the
labels and active subset without tags or allocation identities. Since
$[D_0]=[D_1]$, this quotient is independent of the bits at macro-cuts.
The ordered slots distinguish $C,D_0,D_1$ and recover their bits. The
intermediate quotient during a two-event insertion need not be
bit-independent. Event counting gives the stated grades. $\square$

For a native recorder $R$ put $K_0=J_R(\mathrm{prep}_k)$ and
$K_i=J_R(\mathrm{prep}_k\,\mathrm{insertions}_{1:i})$ at macro-cuts.
This $K_0$ is fixed independently of the unknown bits and order. A
coding decoder first forms $U_{k,A}$, applies the native decoder to
$(U_{k,A},K)$, and reads the ordered slots. Update reconstructs that
same current term, performs the two guarded native events through the
native recorder interface, and clears all additional scratch. No old
term or history is retained. With $e_r$ denoting the actual native
record edits on event $r$, on every induced run

$$
c_i=e_{g_0+2i-1}+e_{g_0+2i},\qquad
\sum_{i=1}^m c_i=\sum_{r=g_0+1}^{g_0+2m}e_r,\qquad
\max_i c_i\le2d,
\tag{IV.108}
$$

where $d$ is the maximum single-event payload cost over all prepared
insertion runs for this $k$. Their true induced payload peak equals the
native peak from the prepared cut through these events, including $K_0$,
both subevent cuts and every edit word. Preparation cost remains charged
on the native side; it is not part of the insertion suffix sum. Extra
parsing, reconstruction, addresses, navigation and scratch remain
separately paid, with no constant overhead or workspace bound asserted.

**Theorem 37.2 (restricted and full native fibre applications).** Fix
an admissible deterministic native recorder and $k\ge1$, and take $d$
as in (IV.108). For the selected full-assignment endpoints $t_x=F_1(x)$,
define two different families

$$
R_x^{\mathrm{prep}}=\{J_R(h):h\text{ is a prepared insertion history ending at }t_x\},
\qquad
R_x^{\mathrm{all}}=\{J_R(h):h\in\mathcal H(t_x)\}.
\tag{IV.109}
$$

Each family separately satisfies Theorem 35.1 with $D=2d$, using its
own centroid and ball. Thus (IV.102) and (IV.106) apply with that radius.
If all fibres of either one of these families are word-tree connected,
then

$$
3\cdot2^{2d}-2\ge\left\lceil\frac{2^k}{k+1}\right\rceil,
\qquad d\ge\tfrac12\bigl(k-\log_2(12k)\bigr).
\tag{IV.110}
$$

In particular logarithmic native payload updates force exponentially
many branch-crossing assignments in each family's own common cut.

**Proof.** The prepared family is the all-history terminal family of
Proposition 37.1's coding restriction. Equation (IV.108) and Lemma 34.2
give edge witnesses at distance at most $4d$. Finiteness follows from
the finitely many orders and bits and finite deterministic runs.
Nonemptiness follows from the preparation. All $t_x$ have the same
$U_{k,[k]}$ and distinct ordered slots, so exact native decoding makes
their record sets disjoint. This verifies all premises for that family.

For the full family prove the premises again. Every $t_x$ has grade
$5k+4$. At every finite grade a finite term has finitely many enabled
addressed events, so induction on grade gives finitely many legal
histories of that length. Hence each $R_x^{\mathrm{all}}$ is finite;
it is nonempty because it contains its prepared histories. If a word
belonged to two such fibres, the same native decoder input
$(U_{k,[k]},J)$ would return the two distinct $t_x$, a contradiction.
Finally the prepared edge witnesses are themselves legal full native
histories, so they belong to these full sets and still have distance
at most $4d$. Theorem 35.1 therefore applies directly to the full sets.
Corollary 35.2 gives (IV.110) under the stated connectivity hypothesis,
and its logarithmic consequence with $D=2d$ gives the claimed count.
The bound $d$ is attained on some prepared suffix event, since that
family of deterministic runs is finite. $\square$

Connectivity is not inherited by restriction: $\{\varepsilon,0,1\}$
is connected but its subset $\{0,1\}$ is not. Nor must restricted
fragmentation persist on enlargement; extra words may enter the ball
and join the branches. The two applications above establish their
premises independently and do not identify their cuts. Taking connected
hulls would add possibly unreachable words and can destroy disjointness.
Connectivity of legal histories under adjacent swaps likewise supplies
no word-tree connectivity without a path-preserving record map.

## 38. Suppliers and unresolved scope of the separator

**Definition 38.1 (source-relative contribution and evidence boundary).**
AA17/19 supply the local guards, all legal histories and grade;
§§23–26 supply the quotient and orientation distinction, including
$C,D_0,D_1$. Proposition 37.1 spells out the source-relative preparation
bridge and its four-leaf positional separation. Definition 30.1 supplies
the native paid-tail interface; AAII94 and Theorem 31.2 supply journal
and snapshot methods for cumulative edits, not a logarithmic bound for
each update. The existing
[Hypercube](../../../D5/S3/Combinatorics/Graph/Hypercube.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/Hypercube.scribe.cs)
supply the cube graph, degree and edge count. The existing
[EnabledPathSwapConnectivity](../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean)
is about legal execution histories, while
[MinimumRollbackAlphabet](../../../D5/S0/History/Coding/MinimumRollbackAlphabet.lean)
is about static injective fibre labels. These inspected suppliers do
not establish connectivity of the present record images.

Weighted centroids, cube expansion and separator methods are classical.
For connected fibres the sets are disjoint connected branch sets in
$T^{2D}$ with touching pairs for cube edges, the standard minor-mapping
setting discussed by Marx,
[*Can You Beat Treewidth?*, pp. 88, 91](https://theoryofcomputing.org/articles/v006a005/v006a005.pdf).
The inspected introduction, Definition 2.1, Proposition 2.4 and §3 of
[Wang–Cao–Lv–Lu, *Treewidth of generalized Hamming graph, bipartite Kneser graph and generalized Petersen graph*, v2](https://arxiv.org/html/2403.12549v2)
provide separator/tree-decomposition context, including references to
[Chandran–Kavitha's hypercube treewidth work](https://doi.org/10.1016/j.disc.2005.12.011)
and [Harper's isoperimetric work](https://doi.org/10.1016/S0021-9800(66)80059-5).
For these last two references only publication metadata and the cited
context were checked, not their full theorem texts; no sharper constant
from them is used. The balance here is relative to the original $N$,
and the complete weak expansion and separator proofs are given in
Theorem 35.1. The connected-fibre mechanism is classical, not a new
general graph principle.

The added source-relative deduction retains every history-dependent
representative, counts ball-avoiding fibres across original branches
at one cut, separates this necessity from the terminal-only construction,
and transfers precisely the native payload interfaces. Bounded inspection
of these sources and the completed literature intake found no exact
statement of that combined application; it does not certify exhaustive
absence or research priority. The finite witness is supplied finite
executable evidence, not an asymptotic result or a formal proof. The
appendix contains ordinary proofs and source applications; no fresh
Lean/kernel verification is claimed.

No new physical $U$ acquisition service, hidden retained memory,
source-bound authority, navigation/scratch bound, total-service optimum
or all-native update algorithm follows. The result imposes no
superlinear peak lower bound. The unrestricted all-$k$ exact causal
$O(k)$-peak/$O(\log k)$-worst-update problem, and its native worst-event
counterpart, remain unresolved: (IV.105) and (IV.110) require their
explicit connected-fibre hypotheses. Hard histories may depend on the
recorder and $k$; no common infinite hard history or completion of the
persistent RRO goal is asserted.

## 追加锚（本行以下为增补区）
## 39. Pair capacity for arbitrary-order labelled-bit tails

**Definition 39.1 (the physical pair count).** Use the causal record
contract of Definition 34.1. Thus $k\ge1$ is fixed before the inputs,
$K_0$ is any fixed finite word, every label occurs once in an arbitrary
order with an arbitrary bit, the settled public input is the exact current
set $A$, and the only persistent private record is the visible whole word
$K$. POP and APPEND each cost one, every edit and every intermediate word is
charged, and separately paid scratch is cleared at each logical cut. For a
terminal assignment $x\in\{0,1\}^k$, let $R_x$ contain **all** reachable
terminal words. These fibres may be history-dependent, have many words, and
be disconnected. Put

$$
T_L=\{w\in\{0,1\}^{*}:|w|\le L\},\qquad
\delta(u,v)=|u|+|v|-2|\operatorname{lcp}(u,v)|,
$$

and, for integers $L,D\ge0$,

$$
P(L,D)=\#\bigl\{\{u,v\}\subseteq T_L:u\ne v,
\ \delta(u,v)\le2D\bigr\}.
\tag{IV.111}
$$

The metric $\delta$ is the shortest POP/APPEND distance, so every actual
update path is at least its endpoint distance.

**Theorem 39.2 (edge-specific pair-capacity obstruction).** Every
admissible causal recorder with finite peak $L$ and worst logical update bill
$D$ satisfies

$$
 k2^{k-1}\le P(L,D),
\tag{IV.112}
$$

and, for every $L,D\ge0$,

$$
P(L,D)=
\sum_{t=1}^{L}2^{L-t}
\left(\sum_{d=1}^{\min(2D,t)}2^d
+\sum_{\substack{1\le i,j\le t\\i+j\le2D}}2^{i+j-2}\right).
\tag{IV.113}
$$

Moreover,

$$
P(L,D)\le5\,2^L(2^D-1),
\tag{IV.114}
$$

for all $L,D\ge0$, and the closed form

$$
P(L,D)=5\,2^L(2^D-1)-(D+1)2^{2D}+1
\tag{IV.115}
$$

holds whenever $L\ge2D-1$ (in particular, for every $L\ge0$ when
$D=0$).

**Proof.** Let $e=\{x,y\}$ be a Boolean-cube edge whose differing label is
$j$. Run all other labels first in one fixed order, with their common bits.
The two runs have the same initial word and the same first $k-1$ inputs, so
causality gives the same word $z_e$ immediately before the last insertion.
If internal choices are allowed, choose one allowed outcome of this common
prefix and use that same outcome for the two completions; the all-outcomes
contract makes both completions admissible. Let $u_e\in R_x$ and
$v_e\in R_y$ be the two terminal outputs. Each last
update has at most $D$ actual edits, hence
$\delta(u_e,v_e)\le\delta(u_e,z_e)+\delta(z_e,v_e)\le2D$.
Exact terminal decoding makes $u_e\ne v_e$. If two cube edges selected the
same unordered pair of words, decoding that pair would give the same
unordered pair of assignments, and hence the same cube edge. Thus
$e\mapsto\{u_e,v_e\}$ is injective. This proves (IV.112). The argument uses
no global choice of one representative per assignment and no connectedness
of any $R_x$; an assignment can use different representatives on its
incident edges.

For the count, assign a distinct word pair to its unique lowest common
ancestor $w$. If $w$ has depth $L-t$, there are $2^{L-t}$ choices for it.
If one endpoint is $w$ and the other is $d$ edges below, there are $2^d$
choices for $1\le d\le\min(2D,t)$. Otherwise the endpoints lie in opposite
child subtrees at distances $i,j\ge1$ from $w$, with $i,j\le t$ and
$i+j\le2D$; there are $2^{i-1}2^{j-1}=2^{i+j-2}$ choices. The left/right
roles count each unordered pair once. Summing over $t$ proves (IV.113),
including the empty sum for $L=0$ or $D=0$.

For $D=0$ every count is zero. Assume $D\ge1$. Divide (IV.113) by
$2^L$ and extend the nonnegative sum to all $t\ge1$. An ancestor term of
depth $d$ contributes
$2^d\sum_{t=d}^{\infty}2^{-t}=2$, so these terms contribute $4D$. A
cross-branch pair $(i,j)$ contributes
$2^{i+j-2}\sum_{t=\max(i,j)}^{\infty}2^{-t}=2^{\min(i,j)-1}$. For
$m=\min(i,j)$ there is one diagonal pair and $2(2D-2m)$ off-diagonal
pairs. Therefore

$$
4D+\sum_{m=1}^{D}(4D-4m+1)2^{m-1}=5(2^D-1),
$$

which gives (IV.114). When $t\ge2D$, the inner bracket in (IV.113) is
constant and equals

$$
\sum_{d=1}^{2D}2^d+\sum_{s=2}^{2D}(s-1)2^{s-2}
=(D+1)2^{2D}-1.
$$

If $L\ge2D-1$, every omitted term in the infinite geometric sum has
$t\ge2D$. Its normalized tail is therefore
$2^{-L}((D+1)2^{2D}-1)$, and subtracting it from
$2^{-L}5\,2^L(2^D-1)$ proves (IV.115). For $D=0$, both sides are zero for
all $L$. $\square$

**Corollary 39.3 (near-minimal memory and the $D=1$ boundary).** Exact
terminal decoding gives

$$
2^k\le|T_L|=2^{L+1}-1,\qquad L\ge k.
\tag{IV.116}
$$

Combining (IV.112) with (IV.114) gives the integer necessity

$$
D\ge
\left\lceil\log_2\left(1+\frac{k\,2^{k-L}}{10}\right)\right\rceil.
\tag{IV.117}
$$

Consequently, for any fixed integer additive allowance $c\ge0$, the regime
$L\le k+c$ forces

$$
D\ge\left\lceil\log_2\left(1+\frac{k}{10\,2^c}\right)\right\rceil,
$$

so the worst logical update is logarithmic in $k$ at fixed additive peak
redundancy. These are necessary bounds; they provide no matching coding
construction and do not rule out constant $D$ when an unrestricted linear
peak is available.

For $D\le1$, the concatenation of the $k$ update paths puts every terminal
word within distance $k$ of the same $K_0$. A radius-$k$ ball in the binary
word tree is contained isometrically in a radius-$k$ ball of the infinite
trivalent tree. That ball has $3\,2^k-2$ vertices and $3\,2^k-3$ edges;
its $3\,2^{k-1}-2$ internal vertices have degree three. A distance-two
pair has a unique midpoint, so the number of distance-one-or-two pairs is

$$
(3\,2^k-3)+3(3\,2^{k-1}-2)=15\,2^{k-1}-9.
$$

Thus (IV.112) excludes $D\le1$ for every $k\ge15$ with arbitrary fixed
$K_0$. If $K_0=\varepsilon$, all terminal words lie in $T_k$, and (IV.115)
gives $P(k,1)=5\,2^k-7$; hence the same obstruction excludes $D\le1$ for
$k\ge10$. These are sufficient exclusions, not sharp thresholds, and they
make no claim that every fixed $D>1$ is impossible.

The parameters $k=L=10,D=1$ separate static capacity from update capacity:
$T_{10}$ has $2047$ words for $1024$ assignments, but (IV.112) asks for
$5120$ distinct physical pairs while $P(10,1)=5113$. The model itself is
inhabited at peak $L=k$: initialize $K_0=0^k$, let public $A$ select the
labelled positions in $K$, and rebuild the required tail in paid scratch;
this has exact current decoding, peak $k$, and at most $2k$ paid edits per
arbitrary-order update. With a fixed known arrival order, appending each
new bit gives the separate comparison $L=k,D=1$. Neither comparison is a
construction for the unrestricted logarithmic-update target.

**Theorem 39.4 (prepared native current-term consequence).** Apply the
contract of Definition 30.1 to the known-alpha, beta-left recorder and use
the prepared family of Proposition 37.1. Its explicit marker is

$$
C=\langle\beta,\alpha\rangle,\qquad
M=\langle\langle C,\alpha\rangle,\alpha\rangle
=\langle\langle\langle\beta,\alpha\rangle,\alpha\rangle,\alpha\rangle,
$$

with four leaves. The preparation has exactly $3k+4$ native events, each
insertion has exactly two legal native events, and a full assignment has
grade $5k+4$. At every macro-cut on this family, public $A$ computes the
same $U_{k,A}$ used by the native decoder, and the coding word is literally
$K=J$ after the fixed preparation. No new encoding or canonical native
representative is introduced.

Let $d_{\rm native}$ be the largest actual POP/APPEND bill of one of the two
native suffix events over all prepared orders and assignments, and let $L$
include the preparation, every settled macro-cut, both native subcuts and
every intermediate edit word. The induced labelled-bit recorder has

$$
D_{\rm code}\le2d_{\rm native},\qquad
 d_{\rm native}\ge
\left\lceil\frac12\left\lceil\log_2\left(1+\frac{k\,2^{k-L}}{10}\right)\right\rceil\right\rceil.
\tag{IV.118}
$$

For $L\le k+c$ this is the corresponding logarithmic necessary condition
with $k/(10\,2^c)$. The equality $K=J$ is at every macro-cut; the two
subevent bills are both included in the logical bill, while U acquisition,
address navigation, reconstruction, scratch, source access and all other
physical service remain separately paid. Preparation cost is charged on the
native side and is not hidden in the insertion suffix sum. The native bound
is a necessary condition for this prepared restriction, not an all-native
update algorithm or a claim about a common cube embedding. In particular,
combining $D_{\rm code}\le2$ with (IV.115) gives only the optional prepared
consequence that $L=k$ and $d_{\rm native}=1$ cannot hold for $k\ge30$;
the general bound (IV.118) is the result retained here.

**Definition 39.5 (suppliers and limits).** The LCA decomposition and
trivalent-ball shell count are classical tree counting inside this
application. The existing Hypercube source supplies the cube edge count;
Definitions 30.1 and 34.1, Proposition 37.1 and the published journal/
preparation interfaces supply the native guards, exact current-term
readout, paid-tail accounting and the ordinal $U$-input correspondence.
The bounded source-relative contribution is the edge-specific injection
(IV.112), its all-height count and the consequent near-minimal-memory
inequality, followed by the faithful prepared native mapping. It is not a
new general counting framework, a repetition of the separator theorem in
§35, or a claim that the cited classical suppliers are project inventions.

No global terminal representative choice, common cube embedding, physical
$U$ acquisition service, navigation or scratch bound, total-service optimum,
matching tradeoff, or actual native implementation follows. The unrestricted
all-$k$ $O(k)$-peak/$O(\log k)$-worst-update coding question and its native
counterpart remain open; no all-constant-$D$ impossibility, Lean/kernel
verification, exhaustive originality result or completion of the persistent
RRO goal is asserted.

## 追加锚（本行以下为增补区）

## 40. One selected golden chain and the original atomic consumer

**Definition 40.1 (selected points, gap sites and atomic names).** Put
$\varphi=(1+\sqrt5)/2$ and $s=\varphi^{-1}=\varphi-1$. For every
$i\in\mathbb Z$ define

$$
\begin{aligned}
A(i)&=\lfloor(i+1)s\rfloor,& P(i)&=A(i)+i\varphi,\\
d(i)&=A(i+1)-A(i),& f(i)&=1-d(i),\\
a_i&=\begin{cases}\beta&f(i)=0,\\\alpha&f(i)=1.\end{cases}
\end{aligned}
\tag{IV.119}
$$

All floors have the displayed lower-floor convention, also at negative
indices. A site $i$ of the binary source names the selected **gap**
$[P(i),P(i+1)]$, rather than the point $P(i)$ alone. The orientation and
length unit are fixed. The integral coefficient $i$ is a mathematical
index; it is not an observed origin or a free source address.

The selected lift $(A(i),i)$ is exactly `goldenWindowFiberLift i` in
[GoldenModelSetFibreBridge](../../../D5/S3/Fourier/GoldenModelSetFibreBridge.lean).
Its definition simplifies to (IV.119) for all integer $i$. Its natural
step theorem gives $d(i)=\texttt{goldenMechanicalLetter}(i+1)$ for
$i\ge0$. These are existing suppliers. In particular

$$
P(i+1)-P(i)=\varphi+d(i)=\varphi^2-f(i)
=\begin{cases}\varphi^2&a_i=\beta,\\\varphi&a_i=\alpha.\end{cases}
\tag{IV.120}
$$

Thus $P$ is strictly increasing. The selected set is
$\Lambda_{\rm sel}=\{P(i):i\in\mathbb Z\}$. It has its own adjacency;
the closed-window set is specified separately in Proposition 44.1.

**Definition 40.2 (the finite original consumer).** Use the distinct
atoms, free ordered binary trees and the original operation $\rho$ of
[Fibonacci atomic relation generation, Definitions 2.1 and 3.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md):

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle u,v\rangle)=\langle\rho(u),\rho(v)\rangle.
\tag{IV.121}
$$

For $H\ge1$ and origin $e\in\mathbb Z$, the task is the ordered tuple

$$
\mathcal R_H(e)=\big(\rho(a_e),\ldots,\rho(a_{e+H-1})\big).
\tag{IV.122}
$$

Each beta input produces the actual ordered pair in (IV.121). The tuple
retains the boundaries between the $H$ outputs. If only output frontiers
are requested, encode beta by $0$ and alpha by $1$ and concatenate the
images under $\sigma(0)=01$, $\sigma(1)=0$. The positive result below
supplies the stronger tuple (IV.122). The quantity observation in the
original source assigns weights $2,3$ to alpha, beta; (IV.120) assigns
lengths $\varphi,\varphi^2$. These are two different functions of the
same recovered atom, with no identification of their values.

The existing word identity fixes the generation convention. If
$T_j=\rho^j(\alpha)$, then for $j\ge1$ its flattened leaf word, encoded
beta $=0$, alpha $=1$, is

$$
f(0)f(1)\cdots f(F_{j+1}-1),\qquad F_0=0,\ F_1=1.
\tag{IV.123}
$$

Indeed `subst` and `fibWord` in
[GoldenGapWord](../../../D5/S0/Tower/GoldenGapWord.lean) encode beta
by `true` and alpha by `false`, starting at beta. The supplied
[`fibWord_eq_beatty_floor`](../../../D5/S1/Words/ZeckendorfBeattyBridge.lean)
identifies its position $i$ with $d(i)$, with exactly the $i+1$ floor
shift in (IV.119). Complementing its Boolean names gives (IV.123), with
$\texttt{fibWord}(j-1)$ of length $F_{j+1}$. The original structural
recursion $T_{j+2}=\langle T_{j+1},T_j\rangle$ supplies the same leaf
lengths. This word identity is a supplier, not a new recovery theorem.
The two-sided extension in (IV.119) is explicitly defined; a finite
$T_j$ is not an infinite two-arm source.

The lower mechanical-word and rotation conventions used here are
classical; see Berstel,
[*Sturmian and Episturmian Words*, §3.1, pp. 30–31](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf).
That identification does not supply observations, tree brackets or
source permissions. The source-specific acquisition statements below
are ordinary derivations using these suppliers.

**Definition 40.3 (one actual source and its original marker menu).**
An unknown fixed origin $e\in\mathbb Z$ selects

$$
S_e=\big(f(e),(L_e,R_e)\big),\qquad
L_e(k)=f(e-k-1),\quad R_e(k)=f(e+k+1)\quad(k\in\mathbb N).
\tag{IV.124}
$$

Both rays belong to the one sequence (IV.119), at the same origin.
Use exactly `Source`, `Policy`, `sideCount`, `markerResponse` and
`actualRun` in
[AdaptiveMarkerStoppingTails](../../../D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.lean).
Write $L$ for `false` and $R$ for `true`. A policy chooses the next side
from its fixed seed and the actually retained action/reply history. It
has no other source input. With $c$ previous queries on that side, the
new query compares the pair

$$
\begin{cases}
\big(f(e-c),f(e-c-1)\big)&L,\\
\big(f(e+c),f(e+c+1)\big)&R.
\end{cases}
\tag{IV.125}
$$

The reply is $1$ precisely when both entries are $0$. Thus the marker
tests two adjacent **long** selected gaps. Each actual query advances
just its chosen side count. Histories are stored newest first. The
state $h_n=(\text{actions},\text{replies},\text{stopped})$ at public
attempt horizon $n$ starts at $([],[],0)$. While active it prepends the
chosen side and reply and sets `stopped` to that reply. Once stopped,
$h_{n+1}=h_n$; no policy or source is read at later horizons.

The corresponding `nativeStep` in
[FiniteAtomLinearRealization](../../../D5/S3/Observer/ProbabilisticClosure/FiniteAtomLinearRealization.lean)
emits `zero` on an unmarked query and, under `Task.raw`, `rawMark` on
the marker. A later native query emits `reject` and leaves the same
state. Such a rejection is not a new source sample. Under
`Task.retained`, the terminal mode is `root(recoveredRoot h)`; under
`Task.raw`, it is merely `stopped`. A residual `Test` introduced afresh
at $h_n$ receives only the current mode and subsequent outputs, with
no earlier trace. A `Test` initialized at $h_0$ can instead retain its
own choices and outputs through its `Test.query` continuation branches;
it need not read the stored `State` lists directly.

**Assumption 40.4 (acquired port and readout contract).** The mathematical
record results refer to the actual $h_n$ just defined. To apply them to
a geometric acquisition, suppose an actually bound handle refers to one
pointed selected chain, with the orientation, calibration and marker
comparison (IV.125). Its two cursors start at that same anchor and obey
the side counts; the handle, cursors and replies remain bound to that
source throughout the run. The controller has the specified query
rights and progress, and preserves every actual action, reply and stop
flag. For results that read $h_n$, access to that complete record and
its finite postprocessing is supplied. A public attempt clock may
select $n=4$ without changing the native stop flag. The seed, controller,
clock, references, records and source-independent scratch carry no
additional $e$-dependent advice. Random seeds, if used, have a law
independent of $e$.

This is a mathematical port premise, not an assertion of physical
installation. There is no reset, extra sample, independent second arm,
postselection, free phase/origin read or new source output after
absorption. Evaluating (IV.122) as syntax is a finite function of
recovered atoms. Executing those operations on an original native tree
additionally requires that actual tree reference, its known operand
addresses or supplied scaffold, current edit rights, lawful phase,
backing, writer, owed-action and return contract. The original AA/AAII
contracts and all the earlier native-history fibres in this volume
retain those premises. The selected-gap port does not provide them.

## 41. Sharp root identification and a different stopping horizon

**Theorem 41.1 (every-policy root and stopping bounds).** For every
$e\in\mathbb Z$, every policy of Definition 40.3 and every fixed seed,
the source $S_e$ satisfies `noAdjacentOnes` and $h_5$ is stopped. The
existing `recoveredRoot` equals $f(e)$ at $h_5$ and every later horizon.
With complete retained-record access, define

$$
D_4(h_4)=
\begin{cases}
\operatorname{recoveredRoot}(h_4)&h_4.\mathrm{stopped}=1,\\
\#_L(h_4.\mathrm{actions})\bmod2&h_4.\mathrm{stopped}=0.
\end{cases}
\tag{IV.126}
$$

Then $D_4(h_4)=f(e)$. For **each** policy and fixed seed, some
nonnegative origin remains active through four attempts and first
marks at five. No policy with a decoder of its complete record can
identify $f(e)$ uniformly over nonnegative origins in at most three
attempts. The latter impossibility also holds for source-independent
randomized control with exact recovery required almost surely at
every origin.

**Proof.** For every integer $u$ and positive integer $m$, telescoping
the displayed floors gives

$$
\begin{aligned}
\sum_{i=u}^{u+m-1} f(i)
 &=m-\lfloor(u+m+1)s\rfloor+\lfloor(u+1)s\rfloor,\\
\lfloor ms\rfloor
 &\le \lfloor(u+m+1)s\rfloor-\lfloor(u+1)s\rfloor
 \le\lceil ms\rceil.
\end{aligned}
\tag{IV.127}
$$

These are ordinary mechanical-word floor estimates, including every
integer boundary. Since $1<2s<2$, every adjacent pair of $f$ has at
most one $1$. Since $1<3s<2$, every triple has at least one $1$.
Since $3<5s<4$, every length-five block has at most two $1$s. Thus

$$
11,\qquad 000,\qquad 10101
\quad\hbox{do not occur in }f.
\tag{IV.128}
$$

The first exclusion proves the exact `noAdjacentOnes` premise on both
rays, including edges incident to the common root.

If $q$ actual queries have all replied $0$, let $l,r$ be their left and
right counts. Each compared edge is neither $11$ nor $00$, and hence
alternates. Because the two rays are opposite portions of one source,
their union is the contiguous interval

$$
f(e-l)\cdots f(e+r),\qquad l+r=q.
\tag{IV.129}
$$

Every edge in that interval has been compared, regardless of query
interleaving. At $q=5$ it would be an alternating six-letter word.
Each such word contains $10101$, contradicting (IV.128). Consequently
the fifth attempt has already marked. At an actual stopped state use
the pointwise supplier
[`stopped_root_recovery`](../../../D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.lean)
on this very $S_e$ and its proved `noAdjacentOnes`. This supplies the
claimed root without a probability-law premise. Absorption supplies
all later horizons. No new conditional root-recovery principle is
being asserted.

If $h_4$ is active, all four attempts were actual queries. Its five
letters alternate. The excluded word $10101$ leaves only $01010$ in
(IV.129). The root is $l$ positions from its left end, so $f(e)=l\bmod2$.
If already stopped, the same supplier applies. This proves (IV.126).
The decoder does not set `stopped` or create a marker at attempt four.

For sharpness, the exact canonical block is

$$
f(2)\cdots f(8)=0010100.
\tag{IV.130}
$$

Fix a policy and seed and follow its four-action replay in which all
replies are $0$. Let $l$ be the resulting left count. At origin
$e=l+3$, the four queried edges lie inside $f(3)\cdots f(7)=01010$.
Induction on the replay shows that all four actions really occur
with zero replies on that source. The next query, on either side,
adds the $0$ at index $2$ or $8$ to a zero endpoint. It marks.
Thus every such policy has worst stopping horizon five.

For the three-attempt lower bound, take its three-action zero replay
and let its left count be $l$. The two origins $e_0=l+3$ and $e_1=l+4$
give observed intervals $f(3)\cdots f(6)=0101$ and
$f(4)\cdots f(7)=1010$. Both produce exactly the replay's actions,
three zero replies and an active flag. Their roots, at the same
offset $l$, are opposite. Any earlier readout has the same inputs on
these sources too. Therefore no decoder succeeds on both.

For a randomized policy, the third-attempt zero replay has only eight
possible action words. At least one has positive seed probability.
Use the same two origins for that word and couple the seed identically.
On this event the entire available record and seed agree, and the
correct roots differ. The sum of the two error probabilities is at
least the event probability, so exact almost-sure recovery at every
origin is impossible. The finite block (IV.130), and all later finite
witnesses, follow directly from (IV.119): for $n>0$ its floors can be
certified by

$$
\lfloor ns\rfloor=q
\quad\Longleftrightarrow\quad
(2q+n)^2<5n^2<(2q+2+n)^2\quad(q\ge0).
\tag{IV.131}
$$

Irrationality makes both comparisons strict. $\square$

**Proposition 41.2 (the readout domain is substantive).** The terminal
`Task.retained` root test receives $f(e)$ by horizon five. A
fresh residual `Task.raw` decoder introduced at public horizon
four, with only `currentMode` and subsequent outputs and no earlier
trace or controller memory, cannot uniformly identify $f(e)$, even
after the known always-right policy. An initialized always-right raw
controller, or a finite `Test` started at $h_0$, does recover $f(e)$
for every $e\in\mathbb Z$ with at most four queries: on the first
`rawMark` at query $k\le4$ return $(k-1)\bmod2$; if the first four
outputs are `zero`, return $0$. Neither the uncomplemented mechanical
letters nor independent outward rays can replace (IV.124) in
Theorem 41.1.

**Proof.** At a stopped state `currentMode retained` is exactly
`root(recoveredRoot h)`; applying the read function that returns its
root bit gives $f(e)$ by Theorem 41.1.

For the fresh residual impossibility, (IV.119) gives
$f(1)f(2)f(3)=100$. Under always-right, origins $e=1$ and $e=2$
therefore have roots $1,0$ and first marker times $2,1$, respectively.
Both expose only `stopped` under `Task.raw` at $h_4$, and every later
raw query rejects without changing the state. Induction on the
`read`, `query` and `inspect` constructors gives the same result for
every fixed fresh residual `Test` on these two states. The known
policy and public horizon four agree as well. Thus these inputs
cannot determine their different roots.

For initialized control, before the first marker every compared right
edge alternates, since neither $11$ nor an unreported $00$ can occur.
At the first marker at query $k$, its inner endpoint is $0$ at distance
$k-1$ from the root. Hence the root is $(k-1)\bmod2$. If all four
outputs are `zero`, the active five-letter word is $01010$ by the
proof of Theorem 41.1, and the always-right root is its first bit $0$.
The controller returns immediately on a marker and makes no later
query; otherwise it returns after query four. Returning after four
zeros leaves the native state active, preserving the distinct stopping
horizon. The counter starts at one at $h_0$ and is known from the
controller's own query sequence, including when it stops early.

Concretely, a finite `Test` uses `query` on $R$ at each of its four
successive zero-branch depths. At depth $k$, the `rawMark` branch is
a `read` with constant Boolean value $(k-1)\bmod2$; the `zero` branch
continues to depth $k+1$, or to a constant-$0$ `read` at $k=4$.
Other output branches may use any constant `read`, since they are
unreachable on this initialized raw run. These reads ignore their mode
argument. The continuation branches suffice without direct access to
the stored `State` history. An initialized controller may likewise
reconstruct its own action/reply record. All these queries use the
same source, absorbing menu and supplied rights; this observation
supplies no additional source query or operation right.

The uncomplemented $d$ has no $00$, by the two-letter estimate in
(IV.127). Fed directly into a $00$ marker it never marks; it also has
$11$, for instance $d(2)=d(3)=1$, so the no-$11$ premise fails.
For a different common-root carrier, copy the one-sided root word
$f(3)f(4)\cdots=010100\cdots$ outward on **both** arms. Each ray
individually is a genuine golden continuation with no $11$. Four
queries on one ray followed by four on the other all reply $0$; query
nine marks. These are not opposite rays of (IV.119). If merely no-$11$
is assumed, two endlessly alternating outward rays never mark at all.
Thus neither marginal word constraints nor conditional stopped-root
recovery supply the common-source stopping theorem. $\square$

## 42. Four consecutive original atoms from one obtained record

**Theorem 42.1 (actual four-atom acquisition).** With Assumption 40.4's
complete record access and the fixed always-right policy, one actual
run determines

$$
(a_e,a_{e+1},a_{e+2},a_{e+3})
\quad\hbox{and}\quad \mathcal R_4(e)
\qquad(e\in\mathbb Z).
\tag{IV.132}
$$

Let $K$ be the retained number of actual queries at first stop, also
equal to $|h_5.\mathrm{actions}|$. Its exact decoding table is

| $K$ | $f(e)f(e+1)f(e+2)f(e+3)$ | One canonical origin $e$ |
| --- | --- | --- |
| $1$ | $0010$ | $2$ |
| $2$ | $1001$ | $1$ |
| $3$ | $0100$ | $0$ |
| $4$ | $1010$ | $4$ |
| $5$ | $0101$ | $3$ |

All five cases are attained in the one natural generated word.
Consequently any exact summary of this policy's records sufficient for
the task (IV.132) needs at least five values, and the summary $K$ attains
that bound. This counts task-summary values, not the physical memory,
controller state or total cost of acquisition.

**Proof.** Theorem 41.1 ensures $1\le K\le5$. Before its terminal $00$
edge, the root/right word alternates. If $K=1$, the two known letters
are $00$; no $000$ forces the next letter to be $1$, and no $11$
forces the following letter to be $0$. If $K=2$, the known word is
$100$ and no $000$ forces the fourth letter to be $1$. At $K=3$ the
known word is $0100$. At $K=4,5$ the words through the marker are
$10100,010100$, respectively, giving the displayed four-letter
prefixes. The inference of a letter beyond a terminal marker is a
consequence of the fixed source promise (IV.128); it is not an
additional source query.

Exact blocks at the listed origins begin, respectively,
$00101001$, $10010100$, $01001010$, $10100100$, $01010010$.
Thus all rows occur. Substituting each recovered bit by its atom in
(IV.119), and applying precisely (IV.121) to each atom, gives
(IV.132). The two atomic $\rho$ outputs are distinct, so the five
different input tuples also give five different output tuples. Any
sufficient summary must distinguish them. $\square$

**Theorem 42.2 (five atoms cannot be uniformly acquired).** There is no
policy on the original absorbing menu and no postprocessing of its
one actual run, even with its complete trace, arbitrary later horizons,
source-independent auxiliary storage and independent randomized
control, that supplies $\mathcal R_5(e)$ exactly for every nonnegative
origin $e$. The same impossibility holds for the first five atomic
labels and even for their concatenated original-$\rho$ output
frontier. This does not forbid five-label recovery at particular
origins or under additional source advice.

**Proof.** Before the first reply, a fixed seed chooses either $R$ or
$L$. If it chooses $R$, compare $e=20$ and $e=10$. Their first five
bits are, respectively,

$$
00100,\qquad00101.
\tag{IV.133}
$$

Both immediately mark on $R$. Their actual state is identical:
actions $[R]$, replies $[1]$, stopped $=1$. If it chooses $L$, compare
$e=21$ and $e=11$. Their first five bits are

$$
01001,\qquad01010,
\tag{IV.134}
$$

and both have $f(e-1)=f(e)=0$. Both immediately mark on $L$, with
identical actions $[L]$, replies $[1]$ and terminal flag. Each pair
consists of origins of the same sequence. All later states agree by
absorption; every native query afterwards rejects. Source-independent
postprocessing therefore cannot return different answers on the pair.
The atomic tuples differ, and injectivity of the two atomic outputs
in (IV.121) makes their $\mathcal R_5$ tuples differ. Even the flattened
outputs differ:

$$
\begin{array}{c|cc}
\text{first side}&\text{first origin's output}&\text{second origin's output}\\
R&010100101&01010010\\
L&01001010&01001001.
\end{array}
\tag{IV.135}
$$

For independent randomized control let $p$ be the probability of
choosing $R$ first. Coupling the same seed and any later decoder coins
on the right witness pair shows that its two error probabilities have
sum at least $p$. On the left witness pair that sum is at least $1-p$.
One of these is positive. Indeed the worst error over the four fixed
origins is at least $\max(p,1-p)/2\ge1/4$. Exact recovery almost surely
at every origin is therefore impossible. No change to the allowed
menu has been used. $\square$

**Proposition 42.3 (scaffolds and the original tree boundary).** The
recovered four atoms determine $\rho$ of any **supplied known** ordered
binary scaffold filled with those atoms, preserving all scaffold and
beta-output brackets. They do not determine the brackets of an unknown
original tree with that frontier.

**Proof.** Recursive application of (IV.121) to the supplied scaffold
computes its output from its leaves. For the second statement the two
trees

$$
\langle\langle\beta,\beta\rangle,\langle\alpha,\beta\rangle\rangle,
\qquad
\langle\beta,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle
\tag{IV.136}
$$

both have the attained four-letter frontier $0010$. Their left children
are a branch and an atom, respectively. After $\rho$, their left
subtrees are respectively
$\langle\langle\beta,\alpha\rangle,\langle\beta,\alpha\rangle\rangle$
and $\langle\beta,\alpha\rangle$, which still differ. The gap word
supplies no measurement of that structure. The original source's Theorem 5.4 still
recovers composition from its two quantity readings, and Theorem 9.3
still recovers a tree from all its path readings. Neither set of
premises is silently supplied by a flat marker record. $\square$

## 43. The acquired metric segment and its chronological fibres

**Definition 43.1 (a relative chart with its boundary).** At the first
stopped state let $l,r$ be the total left/right counts and $K=l+r$.
For $-l\le j\le r$ write $b_j=f(e+j)$. The rooted oriented chart has
vertices at relative positions

$$
Q(0)=0,\qquad Q(j+1)-Q(j)=\varphi^2-b_j
\quad(-l\le j\le r).
\tag{IV.137}
$$

It includes all $K+1$ visited gap tiles, their $K+2$ endpoints
$Q(-l),\ldots,Q(r+1)$, the root tile $[Q(0),Q(1)]$ and the two end
boundary points. In the selected realization
$Q(j)=P(e+j)-P(e)$. The boundary alone consists only of the two end
points with the indicated orientation; it is a coarser observation
than this full chart. No absolute translation is part of the chart.
The event spine is the chronological side word obtained by reversing
the stored action list.

**Theorem 43.2 (exact reconstruction and the missing interleaving).**
For every source, policy and fixed seed in Theorem 41.1, its actual
terminal transcript determines the chart (IV.137). On the image of
these transcripts, the chart together with its event spine determines
the full original action/reply/stopped record. The chart alone loses
exactly the permitted interleavings of the two outward query chains:
if its terminal side is $L$, their number is
$\binom{K-1}{l-1}$, and if it is $R$, their number is
$\binom{K-1}{l}$. These fibre counts range over all policies capable
of executing the indicated side word, rather than over a fixed
policy's internal seed distribution.

**Proof.** Let $j$ be the last side and $c$ its count **before** the last
query. The terminal compared pair is $00$. All previous compared edges
alternate by (IV.128). Moving $c$ edges inward from the inner zero
endpoint gives root bit $c\bmod2$, precisely the existing
`recoveredRoot` formula. Each other preterminal edge has different
endpoints, so the known root and the stored side order determine both
outward bit strings. The last reply supplies its additional outer zero
endpoint. All $b_{-l},\ldots,b_r$ are thereby known. Substituting
(IV.120) and summing lengths gives (IV.137), including its endpoints.

Conversely the oriented chart recovers its tile bits since
$\varphi\ne\varphi^2$, and it specifies $l,r$ relative to the root.
On this actual terminal image there is just one $00$ adjacency among
visited tiles: the terminal edge. All other compared adjacencies
alternate. That edge is outermost on the last side and identifies
that side (also when $K=1$, using the root). Before it, the two side
chains have respectively $(l-1,r)$ or $(l,r-1)$ edges. Each chain has
one forced outward order. Every shuffle of those preterminal chains
is legal on this same source: it reads only the already specified
alternating edges. Appending the terminal side produces the first
marker at exactly $K$. There are the stated binomial numbers of
shuffles. A fixed scheduled policy can realize each one. No other
side word can have these counts, this final side and the same chart.

Given the event spine, restore its replies as $K-1$ zeros followed
by one $1$, reverse both lists, and set stopped to $1$. This recovers
the actual terminal state. At a later public horizon the state is the
same, so its chart and event spine do not encode the extra elapsed
waiting or rejection chronology. $\square$

**Proposition 43.3 (equal spatial chart, different obtained times).**
There are distinct actual chronological transcripts on one and the
same source with identical rooted metric chart and boundary. Neither
that chart nor its boundary alone determines the query chronology.

**Proof.** At $e=13$, the factor at indices $10$ through $14$ is
$00101$, with root at $13$. The chronological side words

$$
LRLL,\qquad LLRL,\qquad RLLL
\tag{IV.138}
$$

all have replies $0001$, end at $(l,r)=(3,1)$ and visit precisely
$[e-3,e+1]$ in gap-site indices. Their last comparison is between
indices $11,10$, the unique $00$. Their chart is the same five tiles
$00101$, with lengths
$\varphi^2,\varphi^2,\varphi,\varphi^2,\varphi$, and the same root
tile. Their acquired action lists differ. This also attains the
fibre count $\binom32=3$ in Theorem 43.2. $\square$

**Definition 43.4 (which notions of time and memory are recovered).**
The memory in Theorem 43.2 is the obtained marker transcript. Its time
is query order on the fixed selected chain; its space is the relative
tile chart; its boundary is that chart's two endpoints. The mutual
inverse concerns the **supplemented** chart carrying its event spine,
on the actual terminal image. It neither identifies this query order
with the successful $P/S$ generation histories of Definition 1.1 nor
recovers those histories from (IV.123). The four-atom summary $K$ in
Theorem 42.1 is sufficient for its specified consumer under its fixed
policy; it is not a sufficient description for every original native
operation. Reference bindings, orientation, calibration, controller,
clock, retention and postprocessing remain the premises in Assumption
40.4, with their own resources. The chart has no claim of a universal
space/time/memory/boundary inverse or a total-resource minimum.

## 44. Endpoint, source law and reanchoring boundaries

**Proposition 44.1 (the exact closed-window defect).** Let
$\Lambda_{\rm cl}$ be the physical `modelSet goldenWindow` of
[GoldenModelSetDelone](../../../D5/S3/Fourier/GoldenModelSetDelone.lean),
with internal coordinate $a-bs$ and its supplied **closed** window
$[s-1,s]$. Then

$$
\Lambda_{\rm cl}=\Lambda_{\rm sel}\ \sqcup\ \{-1-\varphi\}.
\tag{IV.139}
$$

The additional point splits one selected $\varphi^2$ gap into gaps
$\varphi$ and $1$. Thus the complete closed-set nearest-neighbour
geometry is not globally the selected two-length chain of (IV.120).

**Proof.** At integer coefficient $b$, membership requires

$$
(b+1)s-1\le a\le(b+1)s,\qquad a\in\mathbb Z.
\tag{IV.140}
$$

Unless $(b+1)s$ is integral, this unit interval contains exactly
$A(b)=\lfloor(b+1)s\rfloor$. Irrationality of $s$ makes its integral
case exactly $b=-1$. At that fibre the two integers are $0$ and $-1$.
The first is selected and gives $P(-1)=-\varphi$; the other gives
$-1-\varphi$. Irrationality of $\varphi$ makes the representation
$a+b\varphi$ injective on $\mathbb Z^2$, so the extra point cannot be
selected at another fibre. It lies strictly between
$P(-2)=-1-2\varphi$ and $P(-1)=-\varphi$. Their distances to it are
$\varphi$ and $1$, while their selected separation was $\varphi^2$.
This proves (IV.139). In particular a port on all closed-set neighbours
does not satisfy Assumption 40.4 just by having the same window name.
An actual selection service, an explicit other endpoint convention or
a proved restricted-patch correspondence is needed. The distinct set
named `goldenModelSet = range betaGolden` in
[GoldenModelSetSelfSimilar](../../../D5/S1/Deficit/ModelSet/GoldenModelSetSelfSimilar.lean)
is not identified here with either side of (IV.139). $\square$

**Proposition 44.2 (no transfer of the finite-mixture source law).**
Under any probability distribution on the origins $e$ in (IV.124), the
root/right cylinder $000$ has probability zero. In the existing
`sourceMixture` law with root-one probability $0<p<1$, finitely many
parameters $0<q_i<1$ and positive weights $w_i$ summing to one, its
probability is

$$
(1-p)\sum_i w_i(1-q_i)^2>0.
\tag{IV.141}
$$

Thus that law cannot be substituted for the present generated source.

**Proof.** The absence of $000$ is (IV.128), pointwise in $e$.
The actual `transition` supplier sends $0$ to $1$ with probability
$q_i$ and $1$ to $0$ deterministically. Conditional on root $0$, two
successive zeros on a fixed arm therefore have probability
$(1-q_i)^2$. Weighting by the root probability and mixture weights
gives (IV.141). In addition `conditionalSourceLaw` supplies two
conditionally independent outward Markov trajectories, whereas
(IV.124) supplies opposite parts of one fixed chain. The pointwise
`stopped_root_recovery` used above needs neither law equality nor arm
independence. No finite-atom carrier dimension, mixture identification
or Markov stopping tail is inferred for $S_e$. $\square$

**Theorem 44.3 (one fixed pair defeats reanchored continuation).**
For $e=13,18$, every original policy with the same fixed seed gives
identical complete actual states at every horizon. Every finite
continuation using only their absorbed native marker interface and
source-independent postprocessing also agrees. Nevertheless

$$
f(13+6)=1,\qquad f(18+6)=0.
\tag{IV.142}
$$

Consequently the acquired terminal record does not determine the root
at the six-step-right anchor, even with the full query chronology
retained. With equal prior on these two origins and any independent
randomized controller/decoder its error for that target is at least
$1/2$.

**Proof.** Exact floors in (IV.119) give the common radius-five blocks

$$
f(e-5)\cdots f(e+5)=01001010010\qquad(e=13,18),
\tag{IV.143}
$$

and the opposite bits (IV.142). During the first five attempts every
source index consulted lies within that radius. Inductively identical
records and seed give the same next side, the same compared bits and
the same reply. By Theorem 41.1 both runs have stopped by horizon five.
Absorption then gives equality at every horizon. Their retained root
is $0$ in both cases. A later `nativeStep` produces only `reject`, and
an inspection sees the same mode. Induction on a finite residual test
therefore gives the same result. The same holds for any computation
whose inputs are only this shared record and source-independent data.
Couple all independent random coins identically to get identical
observation laws. Under equal prior the same output distribution
faces opposite required bits, so its average error is at least $1/2$
(exactly $1/2$ for a binary-valued decoder).

Both witnesses occur within the original finite generated word

$$
\operatorname{leafbits}(T_8)
=0100101001001010010100100101001001,
\tag{IV.144}
$$

of length $F_9=34$. This confirms that their differing natural
origins are in one generated leaf word. The infinite source used in
the proof remains the expressly defined two-sided extension; no
extra finite-tree leaves are supplied. $\square$

**Definition 44.4 (a source-bound anchor-transport contract).** An
anchor-transport extension has acquired configurations carrying the
same source handle, old chronological record, current anchor and two
cursors. Its additional transition has source projection
$S_e\mapsto S_{e+1}$, preserves source identity and the old record,
and supplies active cursors whose subsequent queries obey (IV.125)
at that new anchor. Its domain includes the actual reference and
operation rights, backing, clock, progress, rejection and return
conditions authorizing that transition. No transition of this kind
is part of Definition 40.3's absorbed menu. A reset, fresh preparation
or index/phase oracle is a different specified supply.

**Corollary 44.5 (additional source dependence is necessary).** No
extension constructible solely from the acquired terminal record,
absorbed native queries and source-independent postprocessing realizes
six successive exact anchor transports of Definition 44.4 followed
by the original root acquisition, uniformly over the source family.

**Proof.** On $S_{13}$ and $S_{18}$ all the allowed inputs to such a
construction agree by Theorem 44.3. Six exact transports and root
acquisition would return their different bits at the new anchor in
(IV.142), a contradiction. Thus a genuine extension with that consumer
needs an additional source-dependent record or source action that
separates those two realizations. $\square$

**Definition 44.6 (mathematical scope of the source correspondence).**
The earlier AA/AAII operational closures, finite request forests,
original quantity/path recovery and native generation-memory results
use their own sources and acquired contracts. The present task has
the source (IV.124), the obtained record of Definition 40.3 and the
finite original consumer (IV.122). The source-specific assertions in
Theorems 41.1, 42.1–42.2, 43.2 and 44.3 are `repo-derived` ordinary
mathematics. Their suppliers are the existing word identity, the
floor-selected lift, the absorbing execution and the pointwise
conditional stopped-root theorem; none is a new general Sturmian or
root-recovery principle. Physical port realization is the explicit
premise in Assumption 40.4; arbitrary tree brackets and moving-anchor
continuation need the additional structures distinguished in
Proposition 42.3 and Definition 44.4. These finite-domain expressions
of space, query time, boundary and retained memory do not assert a
general inverse between those notions or a universal minimal relation
structure.

## 追加锚（本行以下为增补区）

## 45. A paid continuation at the obtained right cursor

**Definition 45.1 (the unchanged source and the extended raw domain).**
Fix precisely (IV.119)–(IV.125), with $e\in\mathbb Z$ unknown,
beta $=0$, alpha $=1$, the lower floors, increasing right orientation
and selected-chain calibration. The consumer remains $\mathcal R_H(e)$
of (IV.122). Acquire the first marker by the original always-right
`Task.raw` run under Assumption 40.4. Retain its actual first-stop
subrecord, its count $K\in\{1,\ldots,5\}$ and its root certificate.
The first marked edge starts at $p_0=e+K-1$; the actual cursor rests
at its outer site $p_0+1=e+K$. A bound handle and immutable source
version identify this same pointed chain throughout the following domain.

An extended configuration retains that handle/version, original anchor,
orientation, calibration, both cumulative side counts, actual cursors,
the acquisition latch and the whole chronological record $J$.
The left count stays zero in the construction below. At a stopped
configuration a separately supplied, paid operation $\mathsf{Resume}$
may succeed. Its only acquisition-state change is to clear the latch;
it appends a fixed acknowledgement $\mathsf{Ack}$ to $J$. In particular
it preserves $e$, the source/version, original anchor, both counts,
cursors and every old record entry. It returns no source letter,
index, phase, new anchor or refreshed source. With cumulative right
count $c$, an enabled active right query has exactly the transition

$$
b=\mathbf1_{\{f(e+c)=f(e+c+1)=0\}},\qquad
c'=c+1,\qquad \mathrm{latch}'=b.
\tag{IV.145}
$$

It records $R$ and emits `zero` for $b=0$, `rawMark` for $b=1$.
The new cursor is $e+c+1$. A stopped ordinary raw query still emits
`reject`, samples nothing and leaves counts, cursor and latch unchanged.
A Resume while active returns $\mathsf{RefuseActive}$ unchanged;
an invalid or mismatched binding returns $\mathsf{RejectEntry}$ without
a source sample. A supplied grant denial is recorded as $\mathsf{Denied}$
and preserves the stopped configuration. Missing primitive authority
or an unlawful phase disables the call rather than licensing success.
No extra left-query continuation or two-arm anchor transport is assumed.

**Assumption 45.2 (finite supply and returned cuts).** Every claimed
successful finite call has its genuine source-bound rights, valid handle
lifetime, finite backing reserved for its state and record, progress,
acknowledgement and completed return. The controller retains its actual
records, including grants, denials, refusals, rejections and stops.
Record access, finite computation, counters, scratch, output construction
and delivery have their own supplied backing and charges. A pending or
interrupted call is not a successful returned cut. Its actual acquired
prefix is retained; no unreturned block or answer is inferred from it.
The positive conclusions require exactly the finitely many successful
grants and completed queries they use. They assert no physical provision
of this extended port and no fixed finite-capacity realization for all $H$.

For indistinguishability statements, use the fixed monotone schedule:
query right to a mark, successfully Resume with the same fixed Ack,
then query right to the next mark, repeating a specified finite number
of times. Public grant choices, waiting, reference representations and
auxiliaries carry no additional source-dependent advice. This canonical
successful record excludes extra waiting and rejected attempts; the
larger interface still retains such events when they actually occur.
There is no fresh suffix law or independence premise: all comparisons
in (IV.145) read the single fixed source at its retained cumulative count.
The same-cursor acquisition and original-consumer correspondences below
are `repo-derived` ordinary deductions using the stated classical
suppliers; no literature-priority assertion is part of their conclusions.

## 46. From adjacent return words to the actual next comparison

**Theorem 46.1 (same-cursor return correspondence).** Under Definitions
45.1 and Assumption 45.2, suppose a returned stopped cursor is $p+1$
and its marked edge is $f(p)f(p+1)=00$. After one successful Resume,
the next actual marker is reached in exactly $D$ right comparisons,
where $D\in\{3,5\}$. Its inner start is $p+D$, its returned cursor
is $p+D+1$, and its actual reply word is $0^{D-1}1$. The intervening
half-open source block and the newly acquired letters are respectively

$$
B_3=001,\quad B_5=00101,\qquad
f[p,p+D)=B_D,\qquad
f[p+2,p+D+2)=
\begin{cases}100&D=3,\\10100&D=5.\end{cases}
\tag{IV.146}
$$

Here $f[u,v)$ lists the letters at all integer indices $u\le i<v$.
The theorem is pointwise for every integer $p$ in its marked domain.

**Proof.** First fix the supplier correspondence, including its domain.
On natural positions, `goldenWord` true represents $d(i)=1-f(i)$:
the finite-prefix identity in
[GoldenWord](../../../D5/S1/Words/GoldenWord.lean) and
`fibWord_eq_beatty_floor` in
[ZeckendorfBeattyBridge](../../../D5/S1/Words/ZeckendorfBeattyBridge.lean)
give exactly the $i+1$ shift of (IV.119). Thus true-true corresponds
to $00$, and increasing natural indices correspond to increasing
right source indices, with no reversal. The existing
[`golden_return_words_two_true_true`](../../../D5/S1/Words/ReturnWords/GoldenReturnWordsExact.lean)
supplies true-true-false and true-true-false-true-false. Complementing
their names gives $B_3,B_5$. Its adjacent-occurrence definition in
[GoldenReturnWords](../../../D5/S1/Words/ReturnWords/GoldenReturnWords.lean)
includes both marked starts and the absence of any intervening start.
The length injectivity in
[GoldenReturnItinerary](../../../D5/S1/Words/ReturnWords/GoldenReturnItinerary.lean)
ensures that an observed return length identifies its word, rather
than merely its composition.

To use this natural-index supplier at every integer origin, take any
finite block of $N$ letters starting at $u\in\mathbb Z$ and put
$x=\{(u+1)s\}$. For $0\le j<N$ its uncomplemented letters are

$$
d(u+j)=\lfloor x+(j+1)s\rfloor-\lfloor x+js\rfloor.
\tag{IV.147}
$$

The finitely many floors at $j=0,\ldots,N$ are constant on a common
sufficiently short interval $[x,x+\epsilon)$, with $x+\epsilon<1$.
This uses right continuity at an integral floor endpoint as well;
it never replaces a lower floor by an upper floor. The positive
irrational rotation orbit $\{\{(n+1)s\}:n\ge0\}$ is dense, so some
nonnegative $n$ has its phase in $(x,x+\epsilon)$. Equation (IV.147)
then gives exactly the same finite block at $n$. In particular transfer
the entire block $f[p,p+D+2)$ when comparing two adjacent $00$ starts.
Both two-letter endpoint occurrences and every intermediate candidate
start survive the transfer. The supplier therefore classifies these
integer return blocks too. This is the classical mechanical coding
argument of [Berstel, §3.1](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf),
used here only to transport this finite adjacent-marker certificate.

It remains to obtain a next marker with the actual interface. Let
$c=p+1-e$ be the count at the stopped cut. For the $j$th query after
Resume, $j\ge1$, (IV.145) compares $f(p+j),f(p+j+1)$. These are
exactly the replies of the original always-right run mathematically
rooted at $p+1$, at its $j$th query, until its first mark. Induction
on $j$ proves this response correspondence using $c+j-1$ as the
unchanged original count plus the new queries. Theorem 41.1 applied
to $S_{p+1}$ supplies a first mark within five comparisons. This
application is an equality of suffix responses, not a new physical
preparation or an operation moving the original anchor.

Let its marked start be $p+D$. All starts $p+1,\ldots,p+D-1$
were actually compared and unmarked. Thus it is the next adjacent
start after $p$, so the transferred supplier gives $D=3$ or $5$ and
$f[p,p+D)=B_D$. Exactly $D$ comparisons have occurred, because the
first new inner endpoint was $p+1$, not $p$. Appending the final $00$
to $B_D$ and deleting its already known initial two letters gives
$100$ or $10100$. The emitted replies, count and outer cursor follow
from (IV.145). Finite progress and return are Assumption 45.2's
premises; word classification alone supplies neither. $\square$

The adjacent-start convention and derived-word factorization are
classical; see [Justin–Vuillon, §1.2](https://www.numdam.org/item/ITA_2000__34_5_343_0.pdf)
and [Durand, §2.3](https://arxiv.org/pdf/0807.3322v1). The additional
correspondence here is between their half-open block and this paid
operation's outer cursor, actual comparisons and original anchored source.

**Proposition 46.2 (the initial root certificate has a restricted domain).**
The first-stop certificate still gives $f(e)=(K-1)\bmod2$.
Applying the old one-marker `recoveredRoot` to the cumulative lists
of a resumed history is not a sound replacement for that certificate.

**Proof.** The first claim is the alternating-prefix argument of
Proposition 41.2. At $e=2$, the first mark has $K=1$, followed by
$D=5$ in (IV.146). The accumulated right list then has six queries.
The old formula would return $(6-1)\bmod2=1$, whereas $f(2)=0$.
An earlier marker destroys its no-earlier-marker premise. Keeping
the original subrecord or its certified root avoids this false inference;
continued acquisition uses `Task.raw` and the framed blocks. $\square$

## 47. Same-source composition and finite resource bounds

**Theorem 47.1 (the acquired prefix invariant).** Let $p_j$ be the
successive actual marked starts on a canonical successful run, with
$p_0=e+K-1$, and let $D_j=p_j-p_{j-1}$ for $1\le j\le m$.
Define the length-$(K-1)$ word $U_K$ by
$U_K(i)=(K-1-i)\bmod2$ for $0\le i<K-1$. At the returned cut
after exactly $m$ resumed episodes,

$$
\begin{aligned}
Q_m&=K+\sum_{j=1}^{m}D_j,& p_m&=e+Q_m-1,\\
W_m&=U_K B_{D_1}\cdots B_{D_m}00
     =f[e,e+Q_m+1).
\end{aligned}
\tag{IV.148}
$$

There have been exactly $Q_m$ source comparisons and $m$ paid successful
Resumes. The right cursor is $e+Q_m=p_m+1$. The same bound source,
version, original anchor, initial certificate and all old records persist.
Passing to the next returned cut replaces the final $00$ by $B_D00$,
or equivalently appends $100$ for $D=3$ and $10100$ for $D=5$.
Thus $W_m$ is literally a prefix of $W_{m+1}$.

**Proof.** Before the first mark the $K-1$ compared edges alternate,
and the marker's inner letter is zero. Reading backwards from that
letter gives precisely $U_K$, so $W_0=U_K00$ has length $K+1$
and is the indicated original-source prefix. Its cursor and count
are the original returned ones. Suppose the assertion holds at $m$.
Resume changes only the latch and record. Theorem 46.1 then compares
the next $D$ edges of this same source, giving the next adjacent
marker and appending precisely its $D$ previously unacquired letters.
This is the displayed final-$00$ replacement and proves (IV.148) at
$m+1$. It adds $D$ comparisons and one successful Resume, preserves
all old entries, and advances the retained cursor by $D$ sites.
Induction proves every clause.

In particular, splitting a completed run into consecutive groups of
episodes and then concatenating their framed blocks gives the same
word as decoding the whole run: the shared $00$ is retained once,
not appended as a second copy. The intermediate configuration must
be the actual preceding returned cursor on the same version.
Concatenating separately compatible words from unrelated sources
does not satisfy this hypothesis. Refusals and stopped-query rejections
preserve the completed-cut prefix and counts, but add their own record
events; they do not add a $B_D$ block. $\square$

**Corollary 47.2 (every finite original request under finite supply).**
For every finite $H\ge1$, the acquired prefix serves the unchanged
$\mathcal R_H(e)$ whenever $Q_m+1\ge H$. One sufficient uniform budget is

$$
m_H=\max\!\left(0,\left\lceil\frac{H-2}{3}\right\rceil\right),
\qquad Q_{m_H}\le5+5m_H.
\tag{IV.149}
$$

It requires at most $m_H$ successful Resumes and the displayed number
of comparisons, under the finite supply and return premises. The
initial four-atom result of Theorem 42.1 and the nine-atom result below
can give smaller budgets for their respective consumers.

**Proof.** Each $D_j\ge3$ and $K\ge1$, so
$Q_m+1\ge2+3m$. Equation (IV.149) makes this at least $H$.
The upper bound follows from $K\le5$ and $D_j\le5$. Read the first
$H$ bits of (IV.148), replace them by their atoms and apply (IV.121).
This is a finite computation on actually acquired letters.
All constructed counters, retained $J$, references, storage traffic,
query and Ack records, computation, scratch and output remain separately
paid. The bound counts comparisons and successful Resumes only; it
is neither a physical time bound nor a total-resource optimum.
Bounded local block decoding does not bound the memory of $J$, an
unbounded target counter or retained outputs. The quantifier is one
supplied finite execution for each finite request, not a completed
infinite execution with fixed memory. $\square$

## 48. The sharp nine-atom consumer of one successful Resume

**Theorem 48.1 (uniform nine-atom recovery).** After the initial
always-right marker and exactly one successful Resume followed by
the next actual marker, the complete canonical record determines
$(a_e,\ldots,a_{e+8})$ and $\mathcal R_9(e)$ for every $e\in\mathbb Z$.
It uses $K+D_1\le10$ comparisons in total. In addition to its acquired
prefix, the decoder uses the fixed source promise to infer some letters
beyond its current cursor; these are not extra source queries.

**Proof.** Two consecutive distance-three returns would contain
$B_3B_3 00=00100100$. That length-eight block has two ones, but
(IV.127) gives at least $8-\lceil8s\rceil=3$ ones in every such block,
since $4<8s<5$. Hence $3,3$ is impossible. At any marker the prefix
$0010$ is forced by the exclusions $000$ and $11$. If $D_1=5$,
the nine-letter word from $p_0$ is the concatenation of $B_5$ and
$0010$, namely $001010010$.
If $D_1=3$, the following mathematical return exists by the same
source stopping argument and must be five; the nine-letter word is
the first nine letters of $B_3B_5 00$, namely $001001010$.
This use of an unqueried return is a consequence of the source promise,
not a second Resume. Thus in the two cases form respectively

$$
U_K\,001010010,\qquad U_K\,001001010,
\tag{IV.150}
$$

and take the first nine letters. They start at the original $e$,
because $|U_K|=K-1=p_0-e$. Applying (IV.121) gives the required
ordered output tuple with every beta-output bracket retained. The
comparison bound is $K+D_1\le5+5$. $\square$

**Theorem 48.2 (no tenth-atom decoder for this two-marker protocol).**
For the fixed canonical always-right protocol of Theorem 48.1, there
is no decoder of its complete record that returns $\mathcal R_{10}(e)$
uniformly over even the nonnegative origins. Source-independent
auxiliary computation or independent decoder coins do not remove this
obstruction. This is a bound for that specified protocol, without an
assertion of optimality among all possible one-Resume policies.

**Proof.** At $e=2$ and $e=10$ the initial count is $K=1$ and the
next return is $D_1=5$. Both records are the first right `rawMark`,
the same successful Ack and five right replies $00001$, with identical
stop flags and counts. The fixed grants and waiting supply no extra
source channel. Nevertheless their first ten bits are respectively

$$
f[2,12)=0010100100,\qquad f[10,20)=0010100101.
\tag{IV.151}
$$

These blocks occur in (IV.144). Directly, the decisive floors are
$\lfloor12s\rfloor=7$, $\lfloor13s\rfloor=8$,
$\lfloor20s\rfloor=\lfloor21s\rfloor=12$, giving
$f(11)=0$, $f(19)=1$; (IV.131) certifies each floor with integer
square inequalities. Identical available records cannot choose between
these different tenth atoms. Their atomic $\rho$ outputs are distinct,
so their output tuples differ as well. Coupling independent decoder
coins gives the same output law on the two inputs and hence average
error at least $1/2$ under their equal prior. $\square$

## 49. Consumption by the original atom and tree operations

**Theorem 49.1 (the original consumer and a supplied scaffold).**
For any $H$ justified by Theorem 47.1 or 48.1, let $b_0\cdots b_{H-1}$
be the recovered original prefix. The consumer map is exactly

$$
b_i=0\longmapsto a_{e+i}=\beta\longmapsto\langle\beta,\alpha\rangle,
\qquad
b_i=1\longmapsto a_{e+i}=\alpha\longmapsto\beta.
\tag{IV.152}
$$

It yields $\mathcal R_H(e)$ without flattening the boundaries between
its $H$ outputs. For a supplied known ordered $H$-leaf scaffold $C$
with its specified leaf order, it also yields
$\rho(C[a_e,\ldots,a_{e+H-1}])$. A flat acquired prefix does not
in general determine an unknown original bracket structure: for $H\ge3$
the same $H$ labels admit distinct ordered brackets with different images.

**Proof.** The prefix equalities identify each input letter on the
same original source. Equation (IV.152) is the original atomic rule,
and the homomorphic clause of (IV.121) evaluates the supplied scaffold
by structural recursion. This directly uses FARG Definitions 2.1/3.1
and Proposition 42.3, rather than defining a substitute consumer.
For unknown brackets, already the trees $\langle\langle u,v\rangle,z\rangle$
and $\langle u,\langle v,z\rangle\rangle$, with the same three atomic
labels, have different images: the first left image has
$|\rho(u)|+|\rho(v)|$ leaves, the second only $|\rho(u)|$.
For $H>3$, attach the remaining common ordered leaves with the same
outer brackets; the distinction persists. Equation (IV.136) gives
an attained four-letter instance. Further flat letters do not observe
these brackets. Quantity/path recovery retains its original additional
observations. $\square$

**Proposition 49.2 (conditional execution on authentic old operands).**
Suppose an actual AA/AAII installation supplies its genuine current tree
$t=C[a_e,\ldots,a_{e+H-1}]$ at an identified version, together with an
authentic correspondence from the acquired ordered letters to all its
old logical leaf operands. Suppose their acquired addresses are prefix
free, its source/history domain holds, and its current guards, rights,
phase, reservation, backing, writer, acknowledgement and return contract
authorize the original operations. Then one original $P$ at each old
alpha leaf and one original $S$ at each old beta leaf execute $\rho(t)$.
The observation record alone supplies none of these execution premises.

**Proof.** AA Definition 17.1 gives exactly
$P:\alpha\mapsto\beta$ and
$S:\beta\mapsto\langle\beta,\alpha\rangle$ at current logical leaves.
Authenticity of the version and operand map makes the decoded tag the
actual pre-edit tag. Replacing one old leaf cannot change the subtree
at another prefix-free old address. Induction over these distinct old
operands therefore preserves each remaining guard and gives precisely
the homomorphic substitution of Theorem 49.1. The original complete
request semantics, disabled calls, checked refusals and finite return
obligations remain those of AA §20 and AAII §96; no gap-word operation
replaces them. Native history queries require that installation's actual
history records, not $J$ interpreted as a generation journal.

The selected observation source/version remains immutable. If a native
edit changes an object related to it, this proposition uses the acquired
old-version correspondence only for the stated consumption. Reading
again after interleaved edits requires a further proved version and
continuation bridge. Neither cursor continuation nor a word equality
provides that bridge or an installation of the native operations. $\square$

## 50. Ordered geometry, comparison time and retained return memory

**Theorem 50.1 (two exact displacements with distinct quantity weights).**
For a completed return from marked start $p$ to $p+D$,

$$
P(p+D)-P(p)=P(p+D+1)-P(p+1)
=\begin{cases}2\varphi^2+\varphi=\varphi^4&D=3,\\
3\varphi^2+2\varphi=\varphi^5&D=5.\end{cases}
\tag{IV.153}
$$

Thus the marker-start and actual outer-cursor displacements agree.
The original quantities of $B_3,B_5$ are respectively $8,13$, and
their original-$\rho$ quantities are $13,21$. None is a physical
duration or an identification of quantity with selected metric length.

**Proof.** Sum (IV.120) over $B_3$ or $B_5$: they have respectively
$(2,1)$ and $(3,2)$ beta/alpha counts. Shifting the interval by one
deletes $f(p)=0$ and adds $f(p+D)=0$, leaving the same length sum.
The two polynomial identities follow from $\varphi^2=\varphi+1$.
Quantity instead weights alpha by two and beta by three. Its original
substitution weights are three at alpha and five at beta, giving the
four stated integer quantities. $\square$

**Theorem 50.2 (a relative inverse on the canonical successful image).**
Keep the common bound handle/version and calibration as context.
Represent the canonical record by $(K,D_1,\ldots,D_m)$; its full
right-query/reply, fixed Ack and stop sequence is then determined.
It and the relative ordered tiled chart of $W_m$ recover one another,
provided the chart marks its original anchor, starting marker boundary
$p_0$, final cursor and orientation. For the return segment alone,
the ordered list $(D_1,\ldots,D_m)$ and its ordered tiled chart are
mutually recoverable once the starting marker boundary and calibration
are retained. An unlabelled total displacement is a different observation.

**Proof.** From the record use (IV.148) and integrate the lengths
$\varphi^2-b$ from the marked anchor, as in (IV.137). Include the
terminal two zero tiles and their end boundary. Conversely each tile's
length recovers its bit since $\varphi\ne\varphi^2$. The count of
tiles before the marked $p_0$ is $K-1$. Locate successive $00$ starts
through the marked final cursor: their differences are exactly the
$D_j$, because the actual run stopped at each next occurrence.
For a half-open return segment, adjoin the known terminal marker $00$
when parsing its last cell. There are no intervening marked starts
inside a cell. Restore the initial replies $0^{K-1}1$, and for each
subsequent cell restore Ack and $0^{D_j-1}1$. All actions are $R$.
These operations are inverse on their actual canonical image.

This recovers comparison chronology under the fixed successful schedule.
Arbitrary waiting, denied calls, rejections, physical clocks and native
generation histories have not been encoded by this chart. Extra such
events must remain as extra records; they are not reconstructed from
tile lengths. The context binding and rights are not created by the
inverse. $\square$

**Proposition 50.3 (equal totals lose actual order).** Two successful
two-Resume runs have the same initial $K$, comparison count, Resume
count, total return displacement and chart end boundary, but different
ordered words and original output tuples.

**Proof.** Use $e=2$ and $e=7$. Their successive marker starts are
$(2,7,10)$ and $(7,10,15)$, respectively; all are verified directly
in the single word (IV.144). Both have $K=1$, but their return lists
are $(5,3)$ and $(3,5)$. Hence $Q_2=9$ and both use two Resumes.
Their acquired prefixes are respectively

$$
0010100100,\qquad0010010100.
\tag{IV.154}
$$

The return displacements both equal $\varphi^5+\varphi^4$.
Each full ten-tile prefix has seven beta and three alpha tiles, so
its end boundary relative to its root is $7\varphi^2+3\varphi$.
The words differ at offset four, and so do their ordered original
$\mathcal R_{10}$ tuples. Thus totals cannot replace the ordered
record or ordered chart in Theorem 50.2. $\square$

**Proposition 50.4 (new replies separate the old continuation fibre).**
The original collision at $e=13,18$ remains a collision under the old
menu. Under one successful Resume at its always-right first stop,
new actual replies distinguish that pair.

**Proof.** Both initial counts are $K=3$. Their first marker starts
are $15,20$ and their next starts are $20,23$, giving $D_1=5,3$.
Thus the first three resumed replies are $000$ and $001$: the third
new comparison separates them. These marker positions and
$f(19)=1$, $f(24)=0$ follow from (IV.144), so Theorem 48.1 also
recovers their different offset-six letters. Ack itself is fixed and
supplies no distinction. Without Resume there is no new sample and
Theorem 44.3 still applies to every old policy. Its necessity of some
additional source dependence survives; it is not a necessity theorem
for this particular added operation or a minimality claim. $\square$

## 51. Exact induced-source orientation and the generation boundary

**Theorem 51.1 (the actual return-type word at every integer marker).**
At a marked start $p$ put

$$
t=s^2=1-s,\quad a=2t,\quad \ell=s^3=2s-1,\quad
M=\lfloor(p+1)s\rfloor,\quad x=\{(p+1)s\},\quad
y=\frac{x-a}{\ell},\quad q=p-2M-3.
\tag{IV.155}
$$

Then $x\in[a,1)$ and $y\in[0,1)$. Its first return has $D=5$
for $y\in[0,s)$ and $D=3$ for $y\in[s,1)$. At the next actual
marker the induced coordinate is $\{y+t\}$ and the hidden integer
coordinate is $q-1$. Consequently the return-type bit $g=\mathbf1_{D=3}$
and, for any finite $m$ completed returns starting there, their actually
obtained return types satisfy exactly

$$
y=2p-3M+(q+2)s=\{(q+2)s\},\qquad
g_n=f(q-n)\quad(0\le n<m).
\tag{IV.156}
$$

The integer $q$ is an analysis coordinate, not an observer input;
the return word runs in decreasing original indices.

**Proof.** A letter at phase $x$ has $f(p)=0$ just when $x\ge t$.
Then $\{x+s\}=x-t$, so the second zero requires $x\ge2t=a$.
This proves the precise half-open marker cylinder. Rotation by $s$
gives successive phases at steps one, two and three as
$x-t$, $x-2t$, $x+3s-2$, respectively. The first two lie outside
$[a,1)$. The third lies in that interval precisely when
$x\ge a+s^4$. In that case $D=3$ and its new phase is $x-s^4$.
For $a\le x<a+s^4$, step three lies in $[s,a)$; step four has
phase $x+4s-3\in[\ell,t)$ and is still outside. Step five has
phase $x+5s-3=x+s^5\in[a+s^5,1)$ and returns. These computations
also exclude every earlier return. Normalizing by $\ell$ changes
the threshold to $y=s$ and the two increments to $-s$ and $t$.
Hence the induced map is $\{y+t\}$, with exactly the displayed
included lower endpoints. This is the classical induced-return
rotation calculation, here with the source's specified cuts; compare
the lower/upper distinction in
[Klouda–Medková–Pelantová–Starosta, §2.2](https://arxiv.org/pdf/1801.09203v3).

Since $\ell^{-1}=3+2s$, expanding $(x-a)/\ell$ gives
$2p-3M+(p-2M-1)s$, the first equality in (IV.156).
Since $2p-3M$ is an integer and $0\le y<1$, the expression equals
$\{(q+2)s\}$, proving its fractional-part form.
For any integer $q$, the original lower-floor coding satisfies
$f(q)=1$ exactly when $\{(q+2)s\}\in[s,1)$: this is the
image of its $f(q)=1$ phase interval $[0,t)$ after one rotation.
Thus the actual $D=3$ predicate equals $f(q)$, including endpoints.
At a three-step return $M'=M+2$, while at a five-step return
$M'=M+3$. In either case
$q'=p+D-2M'-3=q-1$. Induction gives (IV.156).

The singular integer markers are retained: $p=-3$ gives
$M=-2$, $y=0$, $q=-2$, hence $D=5$ and $f(-2)=0$;
$p=-6$ gives $M=-4$, $y=s$, $q=-1$, hence $D=3$ and $f(-1)=1$.
No all-integer step uses a forward phase identification that drops
these endpoints. The conclusion concerns the specified same-source
returns, without an independent preparation or freely chosen phase.
$\square$

**Proposition 51.2 (original generation through an explicit word boundary).**
Let $\sigma(0)=01$, $\sigma(1)=0$ be the frontier action of the
original $\rho$, and put $\tau(0)=B_5$, $\tau(1)=B_3$.
For an actually acquired finite return-type word $w=g_0\cdots g_{m-1}$,
the original marker-to-marker segment is $\tau(w)$, and

$$
\sigma^3(w)01=01\tau(w),\qquad W_m=U_K\tau(w)00.
\tag{IV.157}
$$

These are frontier word equalities with their displayed boundaries,
not equalities of unknown bracketed trees or native edit histories.

**Proof.** Theorem 46.1 gives the return expansion, and Theorem 51.1
identifies each acquired $g_n$ on the exact original source with its
reversed hidden index. Direct substitution gives
$\sigma^3(0)01=0100101=01\tau(0)$ and
$\sigma^3(1)01=01001=01\tau(1)$. If the first equality in (IV.157)
holds for $u$ and $v$, then
$\sigma^3(u)\sigma^3(v)01=\sigma^3(u)01\tau(v)
=01\tau(u)\tau(v)$. Starting with the empty word proves it for
every finite $w$. The second equality is the actual prefix invariant.
The conjugating boundary is $01$, whereas the acquisition's shared
marker is $00$; they are not interchangeable cuts.

Return expansions, induced codings and morphism conjugacy are classical
methods in the cited return-word literature. Their use here fixes the
source, orientation and boundary in the acquired original-generation
correspondence. The additional premises for tree consumption remain
those of §49. In particular neither (IV.156) nor (IV.157) supplies
unknown brackets, historical selection order, rights to perform
$\rho^3$, or a mutable-source continuation after edits. The relative
space, comparison order, marked boundary and retained record inverses
of §50 have precisely that canonical successful domain; they assert
no universal inverse, physical elapsed time or globally minimal
relation structure. $\square$

## 追加锚（本行以下为增补区）
