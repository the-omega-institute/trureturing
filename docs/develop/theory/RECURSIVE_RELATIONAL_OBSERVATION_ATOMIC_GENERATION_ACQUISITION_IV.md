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

**Definition 18.1 (finite inherited-prefix allocation).** Let $b_1,\ldots,b_m$ be a finite labelled multiset of binary words; repetitions are retained as different tokens. For every binary word $q$ put

$$
D_b(q)=\bigl|\{i:q\preceq b_i\}\bigr|,
\qquad
L^*(b)=\max_{D_b(q)>0}
 \left(|q|+\left\lceil\log_2D_b(q)\right\rceil\right).
\tag{IV.40}
$$

The empty word is included among the possible $q$. A completion is a family of distinct words $x_i$ such that $b_i\preceq x_i$ and the family $\{x_i\}$ is prefix-free. The objective is to minimize $\max_i|x_i|$. The labels matter in the objective's tie-breaking, even when two lower words coincide.

**Lemma 18.2 (exact finite extension optimum).** Every completion in Definition 18.1 has maximum length at least $L^*(b)$. A completion with maximum length exactly $L^*(b)$ exists. It is obtained by processing tokens in decreasing $|b_i|$, breaking ties by a fixed lexicographic order of their labels, and assigning to each token the lexicographically first unused length-$L^*(b)$ word extending its lower word. Thus $L^*(b)$ is the exact inherited-prefix optimum, not merely a Kraft upper bound.

**Proof.** Put $L=L^*(b)$ and first consider any completion with maximum length at most $K$. For a prefix $q$ with $D_b(q)>0$, at least one completed word extends $q$, so any maximum length $K$ first satisfies $K\ge |q|$. The $D_b(q)$ completed words extending $q$ are distinct and prefix-free. Extend each of them, only for counting, to an arbitrary descendant of length $K$. Their depth-$K$ cylinders below $q$ are disjoint, and there are only $2^{K-|q|}$ such descendants. Hence

$$
D_b(q)\le 2^{K-|q|},qquad
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
(e,h)\longmapsto he,qquad b_{e,h}=J(h).
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

## 20. A necessary logarithmic coefficient from the base-4 family

**Theorem 20.1 (base-4 coefficient for every coherent head recorder).** For $r\ge1$, use the native block terms of Definition 13.1 with

$$
 s_i=4^{r-i+1}+1,qquad T_r=t_r,qquad B_r=r(r+1).
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
F(T_r)=\prod_{m=1}^r f_m,qquad
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
T=T(s_1,\ldots,s_r),qquad
N=1+\sum_{i=1}^r(s_i+1),qquad
f_i=\sum_{j=i}^rs_j+r-i,
$$

so that Proposition 13.2 gives $F(T)=\prod_i f_i$. Define

$$
L_{\rm cut}=\sum_{i=1}^r\left\lceil\log_2s_i\right\rceil,qquad
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

**Correspondence 22.1 (what is reused and what is added).** AA §§17–22 and AAII §99 supply the actual known-alpha grammar, complete labelled predecessor partition, event count, native legality, and the acquired source/rights/service hypotheses. Sections 13–16 supply the complete block fibres and the recorder-independent cylinder lower bound. The new ordinary synthesis is Lemma 18.2's exact inherited-prefix allocation installed recursively in Theorem 19.1, together with its full-domain forward inverse and linear bound (IV.43). The base-4 coefficient (IV.49) and certificate ceiling (IV.57) are separate consequences of the same actual native family; they are not claims that the linear recorder is logarithmic.

Cover's [*Enumerative Source Encoding*, §I, Propositions 1–2 and inverse algorithm](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf) supplies static finite-set indexing only. Kaspi–Merhav's [restricted-input formulation](https://arxiv.org/html/1301.0079v1) supplies the mature side-information/prefix-confusability frame. These sources do not supply literal native inherited-prefix coherence, the original seven-request service, or a worst-endpoint logarithmic bound. No worldwide novelty claim is made, and no inaccessible primary theorem is used as a load-bearing premise.

**Correspondence 22.2 (remaining boundary).** Theorem 19.1 proves existence, computability, horizon independence, actual labelled predecessor substitution, full-fibre prefix freedom and the explicit bound
$G(t)\le M_J(t)\le G(t)+N(t)-1$. Theorem 20.1 proves the necessary coefficient $\kappa$ when a logarithmic estimate exists. Theorem 21.2 shows only that the displayed rounded-depth certificate cannot itself yield a superlogarithmic counterexample. The original question—one computable $J$ and one finite $c$ satisfying the logarithmic bound for every actual endpoint, or a universal-class counterexample—therefore remains open in this increment. No Lean/kernel verification, numerical result, total-cost optimum, physical impossibility or completion of the persistent RRO goal is asserted.

## 追加锚（本行以下为增补区）
