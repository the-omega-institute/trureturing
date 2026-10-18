# Recursive relational observation: native entry reference and graft order

> **Reading convention.** This is mathematical reference input with ordinary
> proofs, without Lean kernel certification or a claim of physical realization.
> Numbered statements use the theory-volume template's `generic-v1` convention.
> Published text is preserved; additions and corrections start after the terminal
> append anchor and end with another such anchor.

## 1. Common source and the two different recovery tasks

**Definition 1.1 (ordered source).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\begin{aligned}
h(\alpha)&=h(\beta)=0,\\
h(\langle u,v\rangle)&=1+\max(h(u),h(v)),\\
\rho(\alpha)&=\beta,\\
\rho(\beta)&=\langle\beta,\alpha\rangle,\\
\rho(\langle u,v\rangle)&=\langle\rho(u),\rho(v)\rangle.
\end{aligned}
\tag{ER.1}
$$

Pairing is free and ordered; every bracket and every leaf occurrence belongs
to the source. For a public integer $D\ge0$ put

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
G_u(x)=\langle u,x\rangle,\qquad G=G_\alpha.
\tag{ER.2}
$$

An action word executes from left to right. Thus $\mathsf G\mathsf S$
means first $G$, then $\rho$, where $\mathsf S$ denotes a substitution
commit and $\mathsf G$ a specified left-graft commit.

**Definition 1.2 (unchanged original literal and prediction interface).**
One actual $t\in\mathcal F_D$ remains stationary. A literal Read submits
an arbitrary finite original-root word $a$ over $L,R$, including the empty
word. Its reply $r_t(a)$ is $\alpha$ or $\beta$ at that leaf,
$\mathsf{branch}$ at a pair, and $\mathsf{absent}$ once traversal passes a
leaf. Every such word is legal; prefixes need not have been queried.

Preparation is deterministic, effective, source-blind and independent of a
later target, with common initialization and installed data depending only
on public inputs. It terminates on every source and exports a finite
complete acquired name as in Assumption 1.3. Source information enters
only through charged literal Reads.
After export, the target can be any $R$-starting word $p$ of length at most
$D$. The late reader chooses at most one arbitrary fresh original-root
literal before seeing its reply or any later count. Its final predictor must
return

$$
r_{\rho^k(t)}(p)
\quad\text{for every }t\in\mathcal F_D,\ p\text{ as above},\ k\ge0,
\tag{ER.3}
$$

without another Read, for every subsequently supplied authentic $k$.
The iterates in (ER.3) are prediction targets. Supplying $k$ executes no
substitution. Variable shapes, arbitrary correlated competitors and all the
stated targets remain in this task.

**Assumption 1.3 (complete accessible name and paid cuts).** At any export
or terminal cut, the complete name counts every surviving accessible
source- or history-dependent distinction, including selector and program
control, operands, reply buffers, lengths, allocation, handles, counters,
constant-stock identities, scripts and timing. A displayed small name is
complete only if all other accessible fields are its functions and public
inputs. Handoff, access isolation, source binding, authentication, continuity,
retention and callable access are separately supplied and charged services.
They are not consequences of two leaf atoms or of a cardinality calculation.

**Definition 1.4 (successful work-history target).** The additional work
interface below has histories $(t,w)$, where $t\in\mathcal F_D$ and $w$
is the ordered word of successful work commits. The recovery target is the
pair $(t,w)$ itself, including its empty-word case. Two such histories are
equivalent precisely when both coordinates agree. This target excludes
preparation transactions and their Read transcripts. It is different from
the original prediction equivalence, which identifies sources agreeing in
every value (ER.3), and asks for no actual update word.

## 2. An explicitly acquired, successful work interface

**Assumption 2.1 (paid work realization).** First acquire the complete
literal syntax of the stationary $t$ by original-root Reads. Construct a
work representation $x_0=t$ from those acquired replies. This is a paid
construction of acquired data, with an authenticated relation to the same
source, not an unpriced copy port on the unknown original register. The
original register remains stationary throughout.

Supply a work capability with the two lawful actions

$$
\mathsf S:x\longmapsto\rho(x),\qquad
\mathsf G:x\longmapsto G(x).
\tag{ER.4}
$$

These actions are total and successful on finite work trees. Each commit's
full mathematical output is its action identity, $\mathsf{ok}$ and the new
work tree. The capability binds that successor to the preceding work tree
and source session. Its common source namespace $\sigma$, session epoch
$\nu$, work type and permission $P=\{\mathsf S,\mathsf G\}$ are fixed
comparison fields, not identifiers encoding the unknown syntax or elapsed
history. There is no exposed event counter, timestamp or distinguishing
allocation identity. If an implementation exposes such distinctions, they
belong to its complete name under Assumption 1.3.

The observer already holds the complete current work syntax as acquired
data. It may retain an initial reference $E(t)$, computed before the future
action choices. A paid export after each transaction leaves just the stated
work syntax and reference accessible; transient selector inputs, outputs and
control provide no other retained channel. The additional archive field is
empty for this menu. Access to the current syntax and local decoding remain
charged resources even though they require no further original-source Read.

The selector supplies one legal next action at a time, using public inputs
and already acquired data. All finite choices are admitted. A retained input
script is an archive and is charged; it is not common knowledge of the
decoder. The theorem is uniform over these choices, rather than restricted
to one publicly prescribed update word.

There are no executed failures in this contract. A purported operation
outside the menu is undefined and has no successor or event. Reads,
constant-preparation transactions, resets, copies of the unknown register,
failed attempts and physical timestamps are outside this work-history
domain. These exclusions delimit the target; they do not assert that a
physical executor cannot fail.

**Definition 2.2 (one attained joint image).** Set

$$
\mathcal H_D=\mathcal F_D\times\{\mathsf S,\mathsf G\}^{<\omega},
\qquad X(t,w)=\operatorname{run}_w(t).
\tag{ER.5}
$$

For the height reference, the displayed joint work state is

$$
J_D(t,w)=
(\sigma,\nu,\mathsf{Work},X(t,w),h(t),P,\varnothing).
\tag{ER.6}
$$

Its fields are source/session/type, work syntax, entry reference, permission
and additional archive. The domain of states is exactly
$\mathcal J_D=J_D[\mathcal H_D]$, not the product of their separate ranges.
Acquisition initializes the fields jointly at $w=\epsilon$, and an actual
commit appends its label to $w$ while implementing (ER.4). The fixed fields
and empty archive are common in the comparison. No hidden source field is
available to the decoder. In particular, the source binding in Assumption
2.1 certifies provenance without furnishing a second copy of $t$.

## 3. Exact initial-reference size for the mixed menu

**Theorem 3.1 (height locates the actual entry cut).** For every $D\ge0$,
the map

$$
(t,w)\longmapsto(h(t),X(t,w)),\qquad (t,w)\in\mathcal H_D,
\tag{ER.7}
$$

is effectively injective. Every endpoint fiber $X^{-1}(x)$ has at most
$D+1$ elements, and some endpoint fiber has exactly $D+1$ elements.

More precisely, among all reference encoders $E:\mathcal F_D\to A$
independent of the later word, the smallest attained alphabet
$|E[\mathcal F_D]|$ permitting recovery of every $(t,w)$ from only
$(E(t),X(t,w))$ is exactly $D+1$. Height attains this minimum. Its conditional
fixed-width reference requires $\lceil\log_2(D+1)\rceil$ bits. These are
supplementary-reference counts conditional on the complete current tree.

On the attained image (ER.6), initialization and each action in (ER.4)
are effective, preserve that image and retain the exact work-history target.
This assertion concerns the declared successful work interface only.

Proof. Use the existing substitution-image parser from [PG, §37.2 and
Theorem 44.6][PG] and [JM, Convention 36.2][JM]. Its image grammar is

$$
I=\rho[\mathcal T]::=\beta\mid\langle\beta,\alpha\rangle
                       \mid\langle I,I\rangle.
\tag{ER.8}
$$

The three alternatives are disjoint: $\alpha\notin I$, so the exceptional
pair cannot be a pair of two image trees. The supplied effective inverse
$\delta:I\to\mathcal T$ recovers the unique predecessor under $\rho$.
This parser and substitution injectivity are reused, not new results here.

The image of $G$ consists of pairs with left child $\alpha$. It is disjoint
from $I$: such a pair is neither the exceptional pair nor a pair of two
image trees. Its unique $G$ predecessor is its right child. Consequently
every current tree has at most one predecessor together with its last
action under the two-action menu.

Backward parsing terminates. Indeed, if $A(x),B(x)$ count the two leaf
labels, the positive integer $n(x)=2A(x)+3B(x)$ satisfies

$$
\begin{aligned}
n(\rho(x))-n(x)&=A(x)+2B(x)>0,\\
n(G(x))-n(x)&=2.
\end{aligned}
\tag{ER.9}
$$

Thus the unique predecessor chain from $x$ is finite. Every possible
initial $t\in\mathcal F_D$ giving endpoint $x$ lies on that chain; the
removed action labels give its unique forward suffix $w$. Conversely every
chain point in $\mathcal F_D$, with that suffix, is an admissible history.

Heights never decrease under $\rho$, by induction on the input tree, and
$h(G(x))=h(x)+1$. Each tree in $\mathcal F_D$ has left child $\alpha$,
so cannot lie in $I$. Between two distinct chain points belonging to
$\mathcal F_D$, the nonempty forward segment must therefore end with
$G$. Their heights strictly increase. All initial heights lie in
$\{1,\ldots,D+1\}$, proving the fiber bound and uniqueness of the chain
point of a specified initial height. Parse backward to the end, select that
point, and reverse the removed labels. This is a terminating decoder for
(ER.7); off its attained image it may reject. Forward replay on this
acquired syntax also reconstructs every intermediate tree and the full
declared successful outputs.

For sharpness put $x=G^{D+1}(\alpha)$. The $D+1$ trees

$$
t_j=G^j(\alpha)\in\mathcal F_D\quad(1\le j\le D+1)
\tag{ER.10}
$$

all reach $x$, by $D+1-j$ grafts. These are different recovery targets
with the same endpoint, so every successful $E$ must distinguish all
$t_j$. Height takes all $D+1$ values and supplies the decoder already
proved. The bit assertion follows because $b$ bits have at most $2^b$
values and the height index has a fixed-width encoding.

Finally an action updates $(e,x)$ to $(e,\rho(x))$ or $(e,G(x))$ and
has exactly the output specified in Assumption 2.1. For a representative
$(t,w)$, the successor is represented by $(t,w\mathsf S)$ or
$(t,w\mathsf G)$. Hence it lies in the same actual image. Injectivity
of (ER.7) makes these representative-independent transitions faithful to
the entire initial tree and ordered word. No reverse work permission is
used: backward parsing acts on already acquired syntax. $\square$

## 4. Acquiring the specified reference and pricing its carrier

**Theorem 4.1 (sharp literal price of initial height).** Fix $D\ge1$.
Consider all deterministic source-blind procedures which terminate on every
stationary $t\in\mathcal F_D$ and return exactly $h(t)$, with source
information obtained only by actual original-root literal Reads. Charge
every call, including repeated addresses. For a procedure $A$, let
$T_A(t)$ be calls, $L_A(t)$ the sum of submitted word lengths, and
$H_A(t)$ the maximum submitted length, with zero for an empty query list.
Then

$$
\begin{aligned}
\min_A\max_{t\in\mathcal F_D}T_A(t)&=2^{D-1},\\
\min_A\max_{t\in\mathcal F_D}L_A(t)&=D2^{D-1},\\
\min_A\max_{t\in\mathcal F_D}H_A(t)&=D.
\end{aligned}
\tag{ER.11}
$$

One procedure attains all three bounds simultaneously. At $D=0$ the
height is the public value one and all three minima are zero. This prices
the specified height function; it does not minimize acquisition over every
possible reference attaining the alphabet minimum of Theorem 3.1.

Proof of sufficiency. Reuse [PPF, Lemma 4.1][PPF], whose source-blind
$\operatorname{Acquire}(a,d)$ acquires every reply at $aw$, $|w|\le d$,
using at most $2^d$ actual calls, peak length $|a|+d$ and at most
$(|a|+d)2^d$ submitted letters. Run
$\operatorname{Acquire}(R,D-1)$ on the original stationary tree.

If its attained table has a branch at relative depth $D-1$, the right
subtree has height exactly $D$, using the height promise. Otherwise every
actual path terminates at a labelled leaf by that depth: any deeper path
would pass a branch at depth $D-1$. The greatest reached leaf depth is
then the right-subtree height. Add one. The acquired table therefore gives
the exact output and the upper bounds in (ER.11). It is obtained by actual
full-word queries; no supplied subtree or full table is an input.
Exporting only the height reference uses Assumption 1.3's paid isolation
of the intermediate table, controls and other accessible distinctions.

Proof of necessity. Let $v_0$ be the perfect all-$\alpha$ tree of height
$D-1$, including the one-leaf case $D=1$. It has $2^{D-1}$ leaf
addresses $a$, each of length $D-1$. For each such $a$, replace just that
leaf by $\langle\alpha,\alpha\rangle$ to obtain $v_a$. Both
$t_0=\langle\alpha,v_0\rangle$ and
$t_a=\langle\alpha,v_a\rangle$ belong to $\mathcal F_D$, but their
heights are respectively $D$ and $D+1$.

All literal replies outside

$$
\mathcal C_a=\{Raw:w\text{ is a finite }L/R\text{ word}\}
\tag{ER.12}
$$

agree on $t_0,t_a$. If the actual execution on $t_0$ never enters this
cone, deterministic replay produces the same queries, replies, stopping
decision and output on $t_a$: prove this successively through the finite
run, since every next query is a function of the same acquired information.
That contradicts the different required heights. Thus the one run on
$t_0$ enters every $\mathcal C_a$. These cones are pairwise disjoint,
and every word in them has length at least $D$. This single source
forces at least $2^{D-1}$ calls, $D2^{D-1}$ letters and peak $D$.
Arbitrary off-target queries, absent replies, long addresses and large
workspace do not affect this argument. The zero-query $D=0$ case follows
directly from (ER.2). $\square$

**Convention 4.2 (full acquisition and complete alphabets).** Assumption
2.1 has a concrete sufficient acquisition: use the credited
$\operatorname{Acquire}(R,D)$ and reconstruct $v$ from the obtained
constructor table. The height promise ensures that no reached node at
relative depth $D$ is a branch; recursively replacing each branch by its
two acquired children reconstructs exactly $v$. The wrapper is public.
The sufficient original-source charges are

$$
T\le2^D,\qquad L\le(D+1)2^D,\qquad H\le D+1.
\tag{ER.13}
$$

This is a reuse of PPF acquisition, not a new full-source optimum. Once
$t$ is completely acquired, its height is local computation and incurs
no additional original Read; (ER.11) must not be added again to (ER.13).

Let $Q_D$ count all right-subtree syntax of height at most $D$. Then

$$
Q_0=2,\qquad Q_{d+1}=2+Q_d^2,\qquad |\mathcal F_D|=Q_D.
\tag{ER.14}
$$

Indeed every tree is either one of two leaves or an ordered pair of
height-at-most-$d$ trees. At initialization, if all other distinctions are
isolated as stipulated, the complete retained source-dependent state is
$(h(t),t)$ and has exactly $Q_D$ values, because height is a function of
$t$. It has neither $D+1$ values nor the product $Q_D(D+1)$ values.
Over unbounded update words the attained state alphabet is unbounded:
even one fixed source and successive $G$ commits have strictly increasing
heights. Thus Theorem 3.1 is not a finite-total-memory observer theorem.

**Convention 4.3 (separate resources).** The following coordinates remain
separate from (ER.11) and (ER.13): complete work-tree storage; construction
from the acquired table; reference storage; actual update execution;
literal and reply buffers; submitted-address construction; installed common
code and arithmetic; decoding workspace and output; and the services of
Assumptions 1.3 and 2.1. Source-specific initial code and an optimal-strategy
oracle are not supplied.

For an eager literal representation with $A$ alpha and $B$ beta leaves,
the tree has $2(A+B)-1$ nodes. A $G$ commit adds an alpha leaf and a pair
node. A substitution processes the old syntax, changes each old alpha to
beta, and replaces every old beta by a pair of leaves, increasing node
count by $2B$. Retaining old and new copies during a transaction requires
its actual additional space. These are representation costs, not optimal
time or workspace bounds.

If the current work tree is instead hidden behind a literal port,
Theorem 3.1 needs an additional current-version acquisition. For example,
the existing reached-node traversal queries each of its $2\ell-1$ nodes
for $\ell$ leaves and reconstructs the syntax, charging the sum of the
actual submitted address lengths. Replies from an older version do not
answer current-version queries. No numerical tariff for authentication,
isolation or access follows from these syntax counts.

## 5. Transported grafts create exact same-source order ambiguity

**Definition 5.1 (transported-graft extension).** Fix public $m,r\ge0$,
and set $T_j=\rho^j(\alpha)$ for $j\ge0$. Replace the fixed graft menu
by the following bounded work protocol. After $j$ actual substitution
commits and $a$ actual graft commits, $0\le j\le r$, $0\le a\le m$,
the legal next actions are a substitution if $j<r$, and a left graft
$G_{T_j}$ if $a<m$. A terminal work history has exactly $r$
substitutions and $m$ grafts. Each graft requires a freshly prepared
actual copy of $T_j$ with its construction and delivery charged. A simple
preparation starts with a fresh alpha and performs $j$ substitutions on
that known constant; none is an update of the unknown original source.

Work action outputs are the committed action, direction, exact constant
syntax when present, $\mathsf{ok}$ and successor work tree. No further
timestamps or opaque preparation identities are part of this mathematical
label. The same binding, access, successful-execution and isolation
conditions as Assumption 2.1 apply. Actual receipts confirm commits; a
requested but uncommitted action does not increment a counter or archive.
All other operations are undefined. The target is the ordered successful
work word, with each graft's constant determined by its actual prefix.
The preparation history of that constant is a separate excluded history.

Write $\mathcal W_{m,r}$ for all binary words with $m$ letters
$\mathsf G$ and $r$ letters $\mathsf S$. These are actual selector
inputs, not a retained common script. Let $X_{m,r}(t,w)$ be the endpoint
under the prefix-dependent graft rule.

For all prefixes of these words, the complete displayed code will be
$(x,g,b,R)$, with remaining counts $g=m-a$, $b=r-j$ and the actual
commit-updated record $R$ of (ER.18)–(ER.19). Its joint state includes
the same source/session/work-type fields, work tree $x$, public reference
$(m,r)$, permissions
$P_{g,b}=\{\mathsf G:g>0\}\cup\{\mathsf S:b>0\}$ and archive/counter
record $(g,b,R)$. The state domain is the image of actual acquired
initialization and these paired work/record commits. No tuple with an
unrelated tree, counter or record is admitted merely because each field
occurs somewhere separately. Theorem 5.2 proves recovery and closure on
this image.

**Theorem 5.2 (exact chronology ambiguity and acquired archive).** For
every $D,m,r\ge0$ and every $t\in\mathcal F_D$, all
$\binom{m+r}{m}$ distinct histories $w\in\mathcal W_{m,r}$ are legal and
have the identical complete work-tree endpoint

$$
X_{m,r}(t,w)=G_{T_r}^{\,m}(\rho^r(t)).
\tag{ER.15}
$$

Conditional on this endpoint and the public totals $m,r$, an auxiliary
terminal record permitting recovery of the actual work word needs at
least $\binom{m+r}{m}$ attained values, even when $t$ and any initial
source reference $E(t)$ are also given. This bound is attained on exactly
this family by an archive acquired online from actual successful commits.
The endpoint and archive together also recover $t$ without another
original-source Read.

With the explicit counters and archive described below, every actual
prefix has a jointly attained state closed under its legal successors,
and that state recovers the initial tree and executed prefix. At the
terminal cut the counters are public constants. If the complete retained
name consists only of the endpoint and this archive, its all-source
attained alphabet has exactly

$$
Q_D\binom{m+r}{m}
\tag{ER.16}
$$

values, with the fixed fields of Assumption 2.1 understood. In particular
the binomial count alone is a conditional supplement, not total memory.
Its minimum conditional fixed-width bits are
$\lceil\log_2\binom{m+r}{m}\rceil$.

Proof of the endpoint. At a prefix with $a$ grafts and $j$
substitutions, induction gives the invariant

$$
x=G_{T_j}^{\,a}(\rho^j(t)).
\tag{ER.17}
$$

It holds at the empty prefix. A graft inserts one more outer $T_j$.
A substitution sends every outer $T_j$ to $T_{j+1}$ and the inner
tree to $\rho^{j+1}(t)$, by homomorphism. These are exactly the two
successor cases. Every prefix respects the bounded counters, and each
constant is separately prepared, so every word is legal. At $a=m,j=r$
the invariant is (ER.15). Counting the choices of the $m$ graft positions
gives $\binom{m+r}{m}$ distinct ordered histories.

Proof of necessity. Fix this same actual $t$. Both the endpoint and
$E(t)$ are now fixed, as are the work totals. If two different words
give the same complete auxiliary record, the decoder receives identical
inputs and cannot output both words. Thus that record must distinguish
all $\binom{m+r}{m}$ possibilities. Any surviving script, preparation
stock, control, timing or identity distinctions are part of this record;
putting them outside a displayed archive does not evade the bound.

Proof of online attainment. Order the binary words lexicographically with
$\mathsf G<\mathsf S$. Use the classical enumerative-ranking method
already supplied by [SC, §19][SC], with an explicit commit update here.
Initially set

$$
g=m,\qquad b=r,\qquad R=0.
\tag{ER.18}
$$

Here $g,b$ are remaining graft and substitution counts. On a successful
graft, set $g\leftarrow g-1$ and hold $b,R$. On a successful
substitution, first set

$$
R\longleftarrow
\begin{cases}
R+\binom{g+b-1}{g-1},&g>0,\\
R,&g=0,
\end{cases}
\qquad b\longleftarrow b-1,
\tag{ER.19}
$$

using the old $g,b$ on the right. Both work and record updates commit
together. The legal guards are $g>0$ for graft and $b>0$ for
substitution; no output or successor is assigned to an action failing its
guard. Public exact arithmetic, counters and transient workspace are
additional charged resources.

For a fixed executed prefix, its possible complete extensions form a
lexicographic interval. Inductively its lower endpoint is $R$ and its
length is $\binom{g+b}{g}$. A graft selects the initial block, of length
$\binom{g+b-1}{g-1}$; a substitution skips exactly that block and
selects the subsequent block. When one count is zero there is only one
choice. This proves the interval invariant, including the boundary cases
$m=0$ or $r=0$. At the terminal cut its length is one, so $R$ is
exactly the word's rank, ranging over all integers
$0,\ldots,\binom{m+r}{m}-1$.

The inverse uses the same block sizes: compare a rank with the graft
block size, choose that first letter if it is smaller, otherwise subtract
the block size and choose substitution. Repeating with the reduced
counts recovers the word and hence every $T_j$ graft label. This inverse
is computation on the acquired record, not physical reverse execution.
Replaying the recovered word from the recovered initial tree reconstructs
all intermediate work trees and full declared successful outputs.

For completeness at a nonterminal prefix, the counters give
$a=m-g$, $j=r-b$ and prefix length $a+j$. Unranking the lower endpoint
$R$ gives a completion whose first $a+j$ letters are exactly that prefix,
by the interval invariant. In (ER.17), remove the $a$ known outer
$T_j$ grafts and use the supplied parser $\delta$ exactly $j$ times;
this recovers $t$. Thus $(x,g,b,R)$ recovers the entire actual prefix
target. Its legal transitions use this same $j$, prepare the required
constant, implement (ER.17) and update (ER.18)–(ER.19), so their
successors remain in the joint attained image of these executions.
This establishes closure by construction, not by separately realizing
the tree, counters and archive.

At termination, removing the $m$ known outer grafts and parsing $r$
times recovers $t$. The map $t\mapsto G_{T_r}^m(\rho^r(t))$ is
injective, by ordered-pair cancellation and substitution injectivity.
Every source and every rank is attained by the specified paid execution;
hence their terminal joint range has the product size (ER.16). At this
cut $g=b=0$; all other fields must be isolated or functions of this
code, as Assumption 1.3 requires. The lower and upper alphabet bounds
also give the bit assertion. $\square$

**Corollary 5.3 (no initial reference replaces order acquisition).** If
$m,r>0$, no reference depending only on $t$, even the full initial syntax,
allows recovery of every word in Definition 5.1 from that reference,
the endpoint and the two totals alone. At $m=r=1$ the decisive pair is

$$
\rho(G_\alpha(t))=G_\beta(\rho(t)),
\tag{ER.20}
$$

with respective actual words $\mathsf G\mathsf S$ and
$\mathsf S\mathsf G$. More generally no one finite auxiliary archive
alphabet suffices for all the families $m=r=s$.

Proof. In (ER.20) the initial source and both counts agree, while the
ordered action outputs differ. Theorem 5.2 gives the same obstruction for
every $m,r>0$. For the last assertion the largest binomial coefficient
in row $2s$ is the central one: successive-coefficient ratios are
$(2s-k)/(k+1)$, increasing the coefficients up to the middle and
decreasing them thereafter. As their sum is $4^s$,

$$
\binom{2s}{s}\ge\frac{4^s}{2s+1}.
\tag{ER.21}
$$

The necessary supplementary bits are consequently at least
$2s-\log_2(2s+1)$, an unbounded quantity. $\square$

**Convention 5.4 (constant preparation and retained costs).** The
just-in-time construction in Definition 5.1 consumes one fresh seed and
$j$ known-constant substitution operations per graft made at level $j$.
For a word this is at most $m$ fresh seeds and $mr$ such preparation
updates, in addition to its $m+r$ work commits. This is a sufficient
recipe, not a preparation optimum. If $F_0=0,F_1=1$ and
$F_{i+2}=F_{i+1}+F_i$, the leaf counts of $T_j$ obey
$(A_{j+1},B_{j+1})=(B_j,A_j+B_j)$ from $(1,0)$, so $T_j$ has
$F_{j+1}$ leaves and $2F_{j+1}-1$ literal nodes. Those constant
carriers, their delivery, workspace and consumption are charged as well.

Rank updates need only current actual commits, not an oracle for the
future word. They do require the added authenticated commit-to-record
relation. If preparation identities, exact times or preparation event
order are also recovery targets, Definition 5.1's rank is no longer a
complete archive. If such fields survive as accessible data, their
distinctions are counted even when they are not targets. The terminal
alphabet equality in Theorem 5.2 presupposes their stipulated isolation;
its lower bound holds without that isolation.

## 6. References, prior transcripts and failures have different domains

**Definition 6.1 (scope of an event target).** A work word in this volume
records ordered committed updates only. A prior acquisition transcript
records ordered submitted literals and replies. A full run target can
also record preparation transactions, executed failures, successful Reads,
their outputs, permissions and authentic event identities. These are
different sets of events. An authenticated receipt establishes an actual
commit; a mathematical candidate word does not establish that it occurred.

Theorem 3.1 does not recover the earlier acquisition transcript. The
source $t$ determines replies to a chosen query word, but not which
queries were actually chosen or their order. This is the distinction
already present in [PG, §1][PG] and [SC, §§7 and 18–23][SC].

Likewise, neither recovery theorem extends to erased self-loop events.
For example, if a larger menu permits a work-root Read while leaving
all retained fields fixed, at a pair $x$ that actual event returns
$\mathsf{branch}$ with successor $x$. The empty history and that
one-event history have the same retained state and different event words.
The same issue occurs for an executed failure with unchanged retained
state: its response is a defined $(\mathsf{failure},\text{successor})$,
whereas an illegal unexecuted action has no response or successor. To
include either event, a recovery state must distinguish it from the empty
history and preserve its full response and successor; (ER.6) does not.

This is why Assumptions 2.1 and Definition 5.1 restrict the successful
domain explicitly. They supply no four maps on a failure-bearing run
domain and no reconstruction of physical durations. Fixed-total counts,
a final position and a monotone cost potential do not substitute for
the ordered executed word. The monotone quantity (ER.9) is only the
termination measure for a syntax decoder.

## 7. Mathematical suppliers and literature correspondence

**Convention 7.1 (supplier scope).** Repository references in this volume
designate their committed text at
`5fe79351d430d929eb588422fdf31364c82d9363`. The concrete additions are
the mixed-menu entry separator and its sharp reference size, the literal
price of this specified height function, and the transported-graft
same-source endpoint family with its exact acquired order supplement.
Substitution parsing, paid finite-table acquisition, generic coding,
enumerative ranking, replay and quotient factorization are suppliers.
These are repository-derived ordinary deductions, with no claim of
global mathematical priority or formal certification.

| Supplier | Used correspondence and boundary |
| --- | --- |
| [PG, §§1, 34, 37, 43.1 and 44.1][PG]; [JM, §§36–39][JM] | Ordered writer semantics, actual joint images, substitution parsing, entry-versus-source reference, corrected nonredundancy requirement and explicitly added update/constant-preparation contracts. Theorems 3.1 and 5.2 identify particular fibers of those tree operations. |
| [PPF, Lemma 4.1, Theorems 4.2 and 5.1, Proposition 7.1][PPF] | Paid original-root table acquisition and the already published late-target preparation/name results. Its $2^{D-2}$ preparation optimum for $D\ge2$ is a different objective from (ER.11). The original family is disjoint from $\rho[\mathcal T]$, so an identity source handoff into a predecessor-image runtime is unavailable. |
| [AAR, Theorems 12.3 and 16.3][AAR]; [CBN, Theorem 2.2][CBN] | Full future-$k$ factor trajectories and finite canonical constructor tables already correspond. This is predictive/spatial information, without actual work-event execution or reconstruction of deeper literal labels. |
| [SCE, Theorem 5.2 and Corollary 6.3][SCE] | Target-independent pooling requires $N_D\le m_0 4^q$ for $m_0$ complete names and $q$ fresh Reads. At $D=3$, $N_3=123$ excludes four-name pooling in two Reads. Per-target decoders are not an acquired whole common table. |
| [ActualTreeReadoutAcquisition][ATA], `Source`, `readout`, `Policy`, `paid`, `acquisition_foundation`, and its [owning Scribe][ATAB] | Stationary literal replies and actual acquisition histories. Its `paid` counts distinct addresses, and its strategy output is a third-image-membership Boolean; it does not assert (ER.11)'s per-call height task or an installed work-update service. |
| [FixedTreeCommonExtension][FCE], `Full`, `Implementation`, `result`, and its [owning Scribe][FCEB] | A fixed full coordinate tree, supplied leaf values and supplied full child-message tuples, with an arbitrary correlated promise. These inputs are not charged acquisition of an unknown original tree. |
| [NativeLiteralMoore][NLM], `NativeLiteralFeasible`, `literal_moore_feasibility`, `finite_literal_synthesis`, and its [owning Scribe][NLMB] | Runtime is on `substitution u.val`, with acquired `ImageValues` and whole output `canonicalRow P u.val`. Acquisition, isolation and authenticated continuity remain paid premises; there is no original stationary-family identity port. |
| [SC, §§7 and 18–23][SC] | Existing actual-record acquisition, exact conditional alphabet accounting and enumerative rank updates. Ranking is used inside Theorem 5.2; the new fiber is the concrete transported-graft family. |

**Convention 7.2 (primary literature and hypothesis map).** The following
sources supply mature mathematical mechanisms or comparisons. None supplies
the acquired original-interface four-view theorem.

| Primary source | Exact correspondence and limit |
| --- | --- |
| C. H. Bennett, *Logical Reversibility of Computation*, IBM JRD 17 (1973), 525–532, [author text][Bennett] | The introduction and three-tape construction retain operation records to determine predecessors. Added tapes, copying and reverse computation are supplied operations. Here (ER.8) decodes acquired syntax; no physical inverse is granted, and the reference must also identify the actual entry cut. |
| J. N. Foster et al., *Combinators for Bidirectional Tree Transformations*, TOPLAS 29(3), Article 17 (2007), [§3, PDF pp. 6–7][Foster] | GetPut and PutGet concern get and putback, with partial domains; putback takes the old concrete value as an argument. That argument is already supplied, unlike hidden original-source information. The laws alone do not recover an executed history. |
| I. Lanese, I. Phillips and I. Ulidowski, *An Axiomatic Theory for Reversible Computation*, TOCL 25(2), Article 11 (2024), [arXiv:2307.13360v2][Lanese] | Definition 7.9 and Proposition 7.10 relate sequential backward determinism to BTI in its reversible LTSI setting. Definition 3.2's causal equivalence permits swaps and cancellation; Proposition 3.8 has additional WF/PL hypotheses. That quotient need not retain literal event order. Equation (ER.20) is a transported-constant equality, not a claim that two fixed fully labelled native actions are independent transitions. |
| C. R. Shalizi and J. P. Crutchfield, *Computational Mechanics: Pattern and Prediction, Structure and Simplicity*, [Theorems 1–3, cond-mat/9907176v2][Shalizi] | Predictive sufficiency, entropy minimality and almost-sure uniqueness concern a stochastic process's future distributions. Their state equivalence is not lossless past-history equality or a deterministic worst-case alphabet bound. No source acquisition port or work permission follows. |
| P. van den Bos and F. Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [§§3–4, arXiv:1907.11034v2][Bos] | Compatibility and adaptive tests distinguish states under their declared input/output interface. They do not provide literal-tree Reads, current-version continuity or access to erased event order. |
| H. Kowshik and P. R. Kumar, *Optimal Function Computation in Directed and Undirected Graphs*, [Theorem 1, arXiv:1105.0240v2][Kowshik] | Feasible encoders preserve the function for every side input. This is the coding criterion behind conditional distinctions; it supplies neither the actual endpoint fibers in Theorems 3.1/5.2 nor their acquisition and execution services. |

## 8. Remaining four-view bridge

**Open problem 8.1 (original-task native four-view realization).** On one
actual same-source history domain, construct four concrete natural
expressions for spatial support, ordered executed events, complete lawful
continuation responses and callable memory. They must be jointly acquired,
have lawful selectors and successors, and satisfy the Full/NextCompat
conditions of [PG, §34][PG], or their full run versions if failures are
included. Every view must individually have the intended complete task
kernel, with nonredundancy as required by [PG, Proposition 43.1][PG].
Pairwise recoverability and task sufficiency alone give only the forward
kernel inclusion.

Theorems 3.1 and 5.2 give acquired recovery states for two specified
successful update domains. They do not present four natural views, and
neither endpoint alone is a substitute for its required reference or
archive. The added relation differs between the menus: an acquired
initial-entry separator suffices for (ER.4), while the transported-graft
menu needs information about actual order even with the entire source
given. Enlarging a source-only reference cannot repair (ER.20). Any order
archive must be acquired from actual commits, as in (ER.19), or the menu
must be restricted.

For the original task (ER.3), actual update words on one fixed $t$ are
not requested distinctions. Full literal syntax can also be redundant:
for $D\ge1$, two perfect right subtrees of height $D$ differing only at
one depth-$D$ leaf label have branch replies at every relative target
of length at most $D-1$, for every $k\ge0$, because substitution preserves
each original pair. Yet their complete initial work trees differ.
Consequently neither full syntax nor exact update chronology has here
been shown nonredundant for original prediction. Adding trace recall or
deeper-label access changes the declared task; it cannot silently change
that kernel.

Callable archive reads themselves create actual events. A full-run
extension must define their selectors, legal domains, outputs, failures,
successors, source/session binding and retention on the same joint image.
The height supplement and bounded shuffle rank do not discharge these
obligations or recover arbitrary preparation/read/failure histories.

The original general $M_1(D)$, sharp $\lambda$, effective all-size
certificates and coherent all-resolution reconstruction remain separate
open objectives. Finite successful-update constructions supply no global
coverage, ThreadComplete or whole-edge legality. No physical clock,
universal spacetime or ontological theorem is asserted.

[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[JM]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[PPF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PREPARATION_FRONTIERS.md
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[SCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SELECTOR_COMMON_EXTENSION.md
[SC]: RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md
[ATA]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[ATAB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs
[FCE]: ../../../D5/S3/Observer/Separation/FixedTreeCommonExtension.lean
[FCEB]: ../../../Blueprint/D5/S3/Observer/Separation/FixedTreeCommonExtension.scribe.cs
[NLM]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.lean
[NLMB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.scribe.cs
[Bennett]: https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html
[Foster]: https://www.cis.upenn.edu/~bcpierce/papers/lenses-toplas-final.pdf
[Lanese]: https://arxiv.org/html/2307.13360v2
[Shalizi]: https://arxiv.org/pdf/cond-mat/9907176v2
[Bos]: https://arxiv.org/html/1907.11034v2
[Kowshik]: https://arxiv.org/html/1105.0240v2

## 追加锚（本行以下为增补区）

## 9. Reference-free entrances and a completed-cut ternary source

This appendix uses the same free ordered trees and substitution (ER.1), but
declares a different initialization, evolving source menu and present-literal
task. Its source is the actual register being updated, rather than the
stationary original register of Definition 1.2. The new classification
concerns when that source can retain both an arbitrary seed and an arbitrary
committed command word without a supplementary entry reference. The original
prediction task (ER.3), its initialization and all preceding results retain
their stated domains.

### 9.1 Disjoint images and the location of entry

**Definition 9.1 (compound carrier and labelled ancestry).** Write
$\mathcal C=\{\langle s,t\rangle:s,t\in\mathcal T\}$ and retain the image
$I=\rho[\mathcal T]$ and its effective inverse $\delta$ from (ER.8).
For fixed $a,b\in\mathcal T$ put

$$
U(x)=\rho(x),\qquad L_a(x)=\langle a,x\rangle,\qquad
R_b(x)=\langle x,b\rangle\quad(x\in\mathcal C).
\tag{ER.22}
$$

All these maps preserve $\mathcal C$. In the special case $a=b=\alpha$,
write $L=L_\alpha$, $R=R_\alpha$, $\Lambda=\{\mathsf U,\mathsf L,\mathsf R\}$
and

$$
\mathcal P=\mathcal C\setminus\bigl(U[\mathcal C]\cup
                  L[\mathcal C]\cup R[\mathcal C]\bigr).
\tag{ER.23}
$$

A primitive root in this appendix means an element of $\mathcal P$:
it has no predecessor under this entire three-command menu. This differs
from being primitive for substitution alone. Let
$F_w(x)=\operatorname{run}_w(x)$ for finite words over $\Lambda$,
executed from left to right, with $F_\epsilon(x)=x$. Thus
$F_{vw}=F_w\circ F_v$.
An entry class $E\subseteq\mathcal C$ is an ancestry antichain if distinct
members are never related by $e'=F_w(e)$ with $w\ne\epsilon$.
The actual entry of a history is its stipulated starting element of $E$;
it need not be a primitive root.

**Theorem 9.2 (exact fixed-constant criterion).** For every fixed
$a,b\in\mathcal T$, the three maps in (ER.22) are injective.
Their images on precisely $\mathcal C$ are pairwise disjoint if and only if

$$
a\notin I,\qquad b\notin I,\qquad
(a=\alpha\ \text{or}\ b=\alpha).
\tag{ER.24}
$$

In particular $\alpha$ is the unique shared fixed constant for which
$U,L_a,R_a$ have pairwise disjoint images on all of $\mathcal C$.

Proof. Reuse substitution injectivity and the disjoint grammar (ER.8).
On compound predecessors its exceptional leaf production is excluded, so

$$
U[\mathcal C]=\{\langle i,j\rangle:i,j\in I\}.
\tag{ER.25}
$$

Consequently $U[\mathcal C]\cap L_a[\mathcal C]\ne\varnothing$ if and
only if $a\in I$. For the nontrivial direction choose the other child
to be $\rho(\beta)\in I\cap\mathcal C$. The symmetric intersection with
$R_b[\mathcal C]$ is nonempty if and only if $b\in I$.
Finally ordered-child cancellation gives

$$
L_a[\mathcal C]\cap R_b[\mathcal C]\ne\varnothing
\quad\Longleftrightarrow\quad a,b\in\mathcal C:
\tag{ER.26}
$$

any intersection must be $\langle a,b\rangle$, with both variable arguments
compound, and this tree suffices. Under $a,b\notin I$, the only possible
noncompound constant is $\alpha$, since $\beta=\rho(\alpha)\in I$.
The three intersection tests therefore give exactly (ER.24).
Each graft is injective by free ordered pairing. The shared-constant
conclusion follows by setting $a=b$. $\square$

**Theorem 9.3 (effective forest and exact entry criterion).** For the
$\alpha$-graft menu, evaluation is an effective bijection

$$
\mathcal P\times\Lambda^{<\omega}\longrightarrow\mathcal C,
\qquad (p,w)\longmapsto F_w(p).
\tag{ER.27}
$$

For every $E\subseteq\mathcal C$, the evaluation map
$E\times\Lambda^{<\omega}\to\mathcal C$ is injective if and only if $E$
is an ancestry antichain. If membership in $E$ is decidable, membership
in its attained evaluation image is decidable. If, in addition, $E$ is
an ancestry antichain, every endpoint in that image uniquely and
effectively determines its actual entry in $E$ and its command word.
No entry-dependent reference with one fixed finite alphabet makes
evaluation injective for unrestricted $E=\mathcal C$.

Proof. Theorem 9.2 gives at most one predecessor together with its last
command label. It is effective: test (ER.25) and use $\delta$ on its
children for a $U$ predecessor; test for left child $\alpha$ and compound
right child for an $L$ predecessor; test the symmetric condition for $R$.
These tests are disjoint. A graft whose variable child is a leaf does
not pass the compound-predecessor test.

Use the already supplied positive measure $\nu(x)=2A(x)+3B(x)$ from
(ER.9). A $U$ step increases it by $A(x)+2B(x)>0$, and either graft
increases it by $2$. Every backward step strictly decreases this integer.
The resulting unique finite labelled chain ends at one element of
$\mathcal P$; reversing the removed labels gives (ER.27).
This is a finite syntax computation, not permission to undo the source.

Any two entries reaching one endpoint occur on that same chain. If they
are distinct they are comparable by its nonempty intervening word.
If they coincide their suffix words coincide by uniqueness of the labelled
chain and strict growth. Conversely $e'=F_v(e)$ between distinct entries
gives the collision $(e,v)$ and $(e',\epsilon)$. This proves the
antichain equivalence. For decidable $E$, testing membership at every
point of the finite chain decides whether the endpoint is in its attained
evaluation image. If $E$ is also an ancestry antichain, an attained
endpoint has exactly one such point; the removed suffix supplies its
unique command word. For every history starting in this $E$, that point
is its actual entry, even when the chain continues further back.
Without the antichain condition, more than one chain point can belong
to $E$, and image recognition does not identify the actual entry.

For the last assertion take $p=\langle\alpha,\alpha\rangle\in\mathcal P$.
For each $N\ge0$, the $N+1$ entries $L^j(p)$, $0\le j\le N$, all reach
$L^N(p)$ by different suffixes. A reference depending only on the entry
must distinguish all these entries. Since $N$ is arbitrary, no fixed
finite reference alphabet suffices. This is a supplementary-reference
bound conditional on the endpoint, not a bound on total retained material.
$\square$

### 9.2 One-graft entrances and the stronger root target

**Theorem 9.4 (classification of one-graft entrance classes).** Define
the forward substitution orbit
$\mathcal A_\alpha=\{\rho^k(\alpha):k\ge0\}$.
For every fixed $a\in\mathcal T$, each of the following classes is an
ancestry antichain if and only if $a\notin\mathcal A_\alpha$:

$$
E_a^\ell=\{\langle a,u\rangle:u\in\mathcal T\},\qquad
E_a^r=\{\langle u,a\rangle:u\in\mathcal T\}.
\tag{ER.28}
$$

Proof. Consider $E_a^\ell$. Suppose a nonempty word carries
$e=\langle a,u\rangle$ to $\langle a,v\rangle$.
If it has no graft, it is $\mathsf U^k$, $k>0$, and child cancellation
gives $\rho^k(a)=a$, contradicting strict increase of $\nu$.
Otherwise split it at its last graft as $v'X\mathsf U^k$,
$k\ge0$, and put $y=F_{v'}(e)$.
We have $\nu(y)\ge\nu(e)>\nu(a)$.
If $X=\mathsf R$, the final left child is $\rho^k(y)$, which cannot
equal $a$ by this inequality. If $X=\mathsf L$, that child is
$\rho^k(\alpha)$, so necessarily $a\in\mathcal A_\alpha$.
This excludes every comparison when $a$ is off that orbit.

Conversely if $a=\rho^k(\alpha)$, the nonempty word
$\mathsf L\mathsf U^k$ sends every $e\in E_a^\ell$ to
$\langle a,\rho^k(e)\rangle\in E_a^\ell$.
Strict growth makes these distinct entries, proving failure of the
antichain condition. For $E_a^r$ use right children: a last left graft
would force $a=\rho^k(y)$, and a last right graft forces
$a=\rho^k(\alpha)$. The converse word is
$\mathsf R\mathsf U^k$. $\square$

**Corollary 9.5 (attained one-graft entry and its restricted minimum).**
Put

$$
a_0=\langle\alpha,\alpha\rangle,\qquad
j(u)=\langle a_0,u\rangle\quad(u\in\mathcal T).
\tag{ER.29}
$$

Then $j$ is injective, its range is a decidable ancestry antichain, and
$F_w(j(u))$ uniquely and effectively determines every finite $u$ and
every finite $w\in\Lambda^{<\omega}$.
One fixed whole left graft suffices to initialize all seeds for this
reference-free recovery target. Zero grafts, with the arbitrary compound
source left unchanged as entrance and all future words allowed, do not.
This zero-versus-one minimum concerns only fixed whole-graft initialization
with unchanged arbitrary seeds.

Proof. The grammar (ER.8) excludes $a_0$ from $I$: it is not the
exceptional pair and neither child is an image. Every positive iterate of
$\alpha$ lies in $I$, while $a_0\ne\alpha$, so
$a_0\notin\mathcal A_\alpha$. Theorem 9.4 makes $j[\mathcal T]$ an
ancestry antichain, and its membership test is exactly “a pair with left
child $a_0$.” Apply Theorem 9.3 to this decidable ancestry antichain and
remove the known left child at the selected entry. With no initializer,
any $x\in\mathcal C$ and $U(x)\in\mathcal C$ are comparable allowed
entries and give a
collision. The point $j(\alpha)=R(a_0)$ also shows why the attained
one-graft entrance is not a uniform primitive-root initializer. $\square$

**Proposition 9.6 (uniform primitive-root initialization).** The map

$$
\iota(u)=\langle\beta,\langle\alpha,u\rangle\rangle
\tag{ER.30}
$$

injects all of $\mathcal T$ into $\mathcal P$. It is realized by two
fixed whole left grafts, first $\alpha$, then $\beta$.
Among initializers consisting solely of a fixed sequence of whole left
or right grafts with source-independent constant trees, two are necessary
and sufficient to send every seed in $\mathcal T$ into $\mathcal P$.

Proof. Neither outer child of $\iota(u)$ is $\alpha$, and its right
child $\langle\alpha,u\rangle$ is outside $I$ by (ER.8).
Thus none of the three predecessor tests applies. Cancelling its two
fixed wrappers recovers $u$.
For a single graft with compound constant $a$, choose seed $\alpha$:
the result is the opposite $\alpha$-graft from $a\in\mathcal C$.
For constant $\alpha$, choose any compound seed: the result is already
in its corresponding graft image. The only other constant is the leaf
$\beta$; choose seed $\beta$, giving
$\langle\beta,\beta\rangle=U(\langle\alpha,\alpha\rangle)$ in either
orientation. These cases exhaust both orientations and all constants.
Zero grafts leave leaf seeds outside $\mathcal C$, and also leave
nonroot compound seeds nonroot. The displayed two grafts attain the bound.

This target is stronger than Corollary 9.5's entry antichain target.
Neither lower bound ranges over substitutions during initialization,
source-dependent editing, alternative controllers or alternative primitives.
The startup $\beta$ graft is additional to the ongoing
$U,L_\alpha,R_\alpha$ menu. Indeed every nonempty word of that menu
starting in $\mathcal C$ ends in one of its images, so cannot enter
$\mathcal P$. $\square$

### 9.3 Encoding the evolving source itself

**Definition 9.7 (same-register encoded menu).** Fix the one-graft
initializer $j$ for the rest of the appendix and put
$c=\rho^2(\alpha)=\langle\beta,\alpha\rangle$.
The actual source starts as the supplied unknown $u$, is left-grafted
with one freshly prepared $a_0$, and then undergoes two actual
substitutions. Its initialized value is $r_0=\rho^2(j(u))$.
Its subsequent three source operations are

$$
\widehat U(r)=\rho(r),\qquad
\widehat L(r)=\langle c,r\rangle,\qquad
\widehat R(r)=\langle r,c\rangle.
\tag{ER.31}
$$

Each graft consumes a fresh actual copy of $c$.
The initial $a_0$ graft is a separately supplied startup operation;
it is not one of the ongoing $c$ grafts.
No reset, unknown-source copy, inverse substitution or rebuilding from
a freely supplied source table is included.

**Theorem 9.8 (reference-free source-support recovery).** For every
finite $u\in\mathcal T$ and every finite ternary word $w$, the above
same-register operations give

$$
x(u,w)=F_w(j(u)),\qquad r(u,w)=\rho^2(x(u,w)).
\tag{ER.32}
$$

Each of the current ordered unlabelled node support
$\operatorname{Pos}(r(u,w))$ and the current terminal-path antichain
$\operatorname{LeafPos}(r(u,w))$ uniquely and effectively determines
$(u,w)$ on this attained image. Neither decoder takes an entry height,
elapsed epoch, command count or order archive as an argument.
The corresponding assertion with $\iota$ holds under its separately
executed two-graft initialization.

Proof. Preservation of pairing and commutation of powers of $\rho$ give,
for each $A\in\{U,L,R\}$,

$$
\widehat A\circ\rho^2=\rho^2\circ A.
\tag{ER.33}
$$

For a graft this uses precisely $c=\rho^2(\alpha)$; substitution uses
$\rho\rho^2=\rho^2\rho$. Initialization and induction on actual commits
give (ER.32).
From the full finite support, mark nodes with children as branches and
the rest as leaves, obtaining $\operatorname{sh}(r)$.
Reuse [ABT, Theorem 12.1, (ABT.30)–(ABT.31)][ERABT]:
its effective actual-image decoder sends
$\operatorname{sh}(\rho^2(x))$ to exactly $x$.
Apply Theorem 9.3 with the decidable ancestry antichain
$j[\mathcal T]$ established in Corollary 9.5 and strip its initializer.
The boundary determines the same support by finite prefix closure,
giving its decoder separately.
For $\iota$, use the primitive-root bijection (ER.27) and strip the
two fixed wrappers by Proposition 9.6 instead.

The fixed code depth two is not a measured elapsed epoch. In a mixed
word the graft constants would themselves be substituted by later $U$
steps; (ER.33) nevertheless keeps a fixed outer coding relation.
The ABT decoder is reused only on that actual ordered image.
It grants no recovery of absolute epochs for arbitrary unmarked sources,
and no physical inverse update. $\square$

### 9.4 Acquisition, retained use and the continuation task

**Assumption 9.9 (one actual source and paid capabilities).** Fix one
source occurrence, root port, left/right orientation and owner before
choosing $u$ or any future command. Its canonical initial installation
contains the actual finite tree $u$, not its description as advice.
Declare exclusive owner authority for total actual substitution, the
startup graft and (ER.31), consuming prepared known constants as in
[PG, Definition 44.1][PG]. Add genuine original-root literal Reads with
the four replies of Definition 1.2, now addressing this evolving register.
A Read preserves its current version. Updates acknowledge success; they
do not return a free syntax table.

Supply a paid ternary input port and source-independent finite effective
control with arbitrarily large finite local workspace. The owner can
retain, inspect and copy its acquired local data and issue framed outputs.
The source is locked against updates during each acquisition traversal.
Only one command is acquired between consecutive completed cuts; no
second command arrives before completion of its update, refresh and output.
Every finite command word is admitted, including the empty word.
There are no additional independently varying waits, interrupts, requests,
allocation names, source encodings, preparation identities or consumer
schedules. Constant supply, allocation and local routines follow fixed
canonical rules, so their actual finite behavior is determined by the
data already acquired and the next supplied command.

These are explicit capabilities of this mathematical source model.
The two leaf labels alone supply none of pairing, root access,
substitution, graft rights, input, ownership or workspace.
In particular the graft and input operations are not opcodes established
by [NativeSerialMachine][ERNSM], whose instruction constructors are local
step, Read, substitution and stop. No identification with the guarded
original source or the earlier stationary-source/work-copy interface is
made.

**Construction 9.10 (actual acquisition and current local use).** At the
initial installed $u$, perform a source-blind left-first stationary
traversal. Reuse [NativeFullSourceProducer][ERPROD],
its source control and native source producer theorem, with its
[owning exposition][ERPRODB]. At a branch the actual reply schedules its
left address and saves the right address; acquired children are combined
by local steps. At a leaf the actual reply supplies its label.
The theorem supplies termination for every finite source and precisely
one actual Read at every node in preorder. Unknown subtrees appearing
in its proof invariants are not runtime inputs.

A local receiver records each submitted address and returned reply.
It therefore builds the complete current finite table

$$
\mathsf F(r)=\bigl[(p,r_r(p)):p\in\operatorname{Pos}(r)
                       \text{ in left-first preorder}\bigr].
\tag{ER.34}
$$

Recording, addressing and combining are actual paid local work.
After initial acquisition, perform Definition 9.7's initialization on
that same source port. Traverse its new stationary version to obtain
$\mathsf F(r_0)$, retain it in the owner's current-table slot, and perform
a prescribed local lookup at address $LL$. The lookup scans the retained
finite table; if the address is absent it returns
$\mathsf{absent}$, otherwise the recorded reply. Completeness of the table
makes this correct also below a leaf. No new source Read is used by this
lookup. Release the framed table and lookup reply and enter
$\mathsf{Ready}$.

At each subsequent $\mathsf{Ready}$, acquire the actual next ternary
symbol, prepare its required constant if any, and use that symbol to
actuate exactly one operation (ER.31). Invalidate the old current-table
binding, run the same traversal while the new version is stationary,
replace the current-table slot with its newly acquired table, perform the
same local lookup and release the complete response before returning
to $\mathsf{Ready}$. The source binding of the current-table slot is
the causal relation to this just-finished traversal at the fixed port,
not a free variable timestamp or a second source.

Retain the producer's actual protocol record, with canonical framing,
in separate charged backing. Include actual input symbols, source-call
acknowledgements, Read addresses/replies, prescribed local work, lookups
and outputs in its ordered occurrence word. No history record is an
input to the source controller or to the geometric decoder.
Current table, record, code, buffers, preparation material, retained old
cells and allocator state all belong to the actual joint state and
resource account. Scratch cleanup or retention follows one fixed rule.
The record need not be part of the selected current-memory view below.

Let $J(u,w)$ be the complete joint state reached after this actual
schedule, through the refresh and output for $w$, including the initialized
empty-word cut. It contains the actual source, current table, lookup
result, control, all retained records and material, and their bindings
and rights. This is one jointly realized image, not a product of
independently possible field values. The fixed rules give a finite
deterministic execution for every $u,w$: stationary traversals terminate
by the supplier, known preparations are finite, and each source operation
acts on a finite tree. Each next completed state is exactly $J(u,wa)$.

**Definition 9.11 (current-table and continued-command task).** The task
$Q_{\rm cur}$ is present-source disclosure and continued actuation.
Its present readout at a completed cut is the actually acquired table
$\mathsf F(r)$ and its prescribed local $LL$ result.
The legal actions are exactly the three complete
input/update/refresh/lookup/output transactions, all total on these
completed states. For action $a$ at $J(u,w)$ the complete response is

$$
\begin{aligned}
\operatorname{Resp}(J(u,w),a)=
\bigl(&a,\mathsf{legal},\mathsf{ok},
       \mathsf F(r(u,wa)),\operatorname{lookup}_{LL}\mathsf F(r(u,wa)),\\
     &\Delta\Gamma,\Delta\mathsf{Out},J(u,wa)\bigr).
\end{aligned}
\tag{ER.35}
$$

Here $\Delta\Gamma$ is the actual protocol-record append and
$\Delta\mathsf{Out}$ the actual framed-output append of that transaction.
The last component is the complete original joint successor, including
rights and retained material, not merely a reconstructed view of it.
All such transactions return to $\mathsf{Ready}$; no executed failure
or no-op is included. Symbols outside the declared alphabet have no
response or successor. Finite future words compose these complete
responses. The empty experiment includes the present readout.
Two completed histories are $Q_{\rm cur}$-equivalent when their present
readouts and all these finite responses agree, including lawful domains
and complete successors. A readout is an observation of the already
acquired result, not an extra independently interleavable recall command.

This task is specified by present literal access and continued source
operation, not by asking directly for a past word or seed.
It is different from (ER.3); full current literal disclosure is an
explicit part of its observational strength.

**Definition 9.12 (four actual expressions at completed cuts).** On the
domain $\mathcal H=\mathcal T\times\Lambda^{<\omega}$ indexing precisely
the $\mathsf{Ready}$ cuts just defined, take:

| Expression | Independently specified actual content |
| --- | --- |
| $S(u,w)$ | The current source's ordered unlabelled support $\operatorname{Pos}(r(u,w))$, at the fixed root. No workspace, table, clock, reference or record support is attached. |
| $B(u,w)$ | The terminal-path antichain $\operatorname{LeafPos}(r(u,w))$ of that source: the addresses where actual current descent ends, with colours erased. |
| $T(u,w)$ | The ordered actual protocol occurrences from the installed-source entrance through the completed cut, including initial truthful acquisition replies and actually received command symbols, as specified in Construction 9.10. It has no appended endpoint snapshot and is not physical duration. |
| $M(u,w)$ | The acquired current addressed literal table in the owner-local slot, with its fixed owner, port binding and current local-lookup authority. No seed copy, old command word, chronology rank or past transcript is an additional payload. |

These are projections of one actual process. Their definitions do not
use their desired inverse maps. The table's label erasure and terminal
addresses give acquired finite descriptions of $S$ and $B$ using the
same traversal; they are not free new scanning ports.
The temporal record is acquired by recording actual occurrences.
Access to any such description, its serialization and its decoder work
is charged. A mathematical view value by itself grants no other owner
authority to read the source or the private local slot.

### 9.5 Individual kernels and all completed-command transports

**Theorem 9.13 (completed-cut four-expression recovery).** Under
Assumption 9.9 and Construction 9.10, for each individual
$V\in\{S,B,T,M\}$ and all $h=(u,w),h'=(v,z)\in\mathcal H$,

$$
V(h)=V(h')
\quad\Longleftrightarrow\quad h=h'
\quad\Longleftrightarrow\quad h\sim_{Q_{\rm cur}}h'.
\tag{ER.36}
$$

Every view has a finite effective decoder on its actual image recovering
the same seed, committed word and complete $J(h)$.
All twelve directed same-cut recoveries exist, are inverse in opposite
directions, agree along every route, and preserve the full response
(ER.35) and complete successor for each of the three commands.
These assertions concern exactly the completed-cut domain and task above.

Proof. For $S$, use Theorem 9.8. For $B$, take prefix closure and use
that same theorem. For $M$, reconstruct the labelled finite tree directly
from its actual complete table, then use its support decoder.
For $T$, the initial truthful acquisition determines $u$, and the actual
command-input occurrences determine $w$. Conversely $u,w$ determine
each of these views and the full original joint state by executing the
fixed finite descriptive schedule. This latter computation uses local
descriptions already recovered; it does not reset or copy an unknown
source. It reconstructs retained logs, allocation, buffers, output
records, preparation residue and rights as well as the current tree.
Thus each view separately has equality of $h$ as its kernel.

For clarity, both task-kernel inclusions can be checked individually.
Equal $S$ gives the same $u,w$, hence identical current states and all
complete future responses. In the other direction, task equivalence
includes equal present tables, hence equal labelled current trees and
equal $S$. Equal $B$ gives the same $u,w$ through prefix closure,
hence the same responses; task equivalence gives equal current trees,
hence equal terminal boundaries. Equal $T$ gives the same acquired seed
and command inputs, hence identical responses; task equivalence gives
equal present trees, Theorem 9.8 gives equal $u,w$, and the fixed
schedule then gives equal temporal words. Equal $M$ gives equal current
tables, hence equal $u,w$ and responses; task equivalence includes equal
present tables and their common fixed binding and rights, hence equal
$M$. This proves both inclusions separately for every view, as required
by [PG, Proposition 43.1][PG]. Nonredundancy here already follows from
the present readout, without using hidden successor coordinates to
separate histories.

Let $d_V$ be the described actual-image decoder to $h$ and define
$R_{VW}=W\circ d_V$. Since $d_V(V(h))=h$, on the actual images

$$
R_{WV}R_{VW}=\operatorname{id},\qquad
R_{WZ}R_{VW}=R_{VZ}.
\tag{ER.37}
$$

Every same-cut route decodes and re-encodes the same $h$, proving all
route agreements. For a command $a$, define the induced view successor
$A_a^V(V(u,w))=V(u,wa)$ and compute its output by (ER.35) from
$d_V(V(u,w))$. These maps are defined on the entire attained view
image and have attained successors, because Construction 9.10 actually
acquires $a$, performs (ER.31), finishes its finite refresh and reaches
$J(u,wa)$. Consequently

$$
R_{VW}A_a^V=A_a^W R_{VW},\qquad
\operatorname{Resp}_a^W R_{VW}=\operatorname{Resp}_a^V.
\tag{ER.38}
$$

The response equality includes the actual input, acquired outputs,
record/output appends and original $J(u,wa)$ in (ER.35).
Induction gives compatibility for every finite future command word.
No equation transports an interrupted traversal or internal source-write
cut. These are finite recovery algorithms on acquired descriptions,
not an installed arbitrary-view delivery or physical reversal service.
$\square$

### 9.6 The same-run account and the remaining domains

**Proposition 9.14 (explicit construction charges).** Write
$\lambda(t)=A(t)+B(t)$ and $N(t)=2\lambda(t)-1$ for the literal occurrence
node count. For seed $u$ and word $w=a_1\cdots a_k$, put
$x_i=F_{a_1\cdots a_i}(j(u))$ and $r_i=\rho^2(x_i)$, including $i=0$.
The specified execution has exactly

$$
\begin{aligned}
N_{\rm Read}
 &=N(u)+\sum_{i=0}^{k}N(r_i),\\
L_{\rm addr}
 &=\sum_{p\in\operatorname{Pos}(u)}|p|
   +\sum_{i=0}^{k}\sum_{p\in\operatorname{Pos}(r_i)}|p|,\\
\lambda(r_i)&=\nu(x_i),\qquad N(r_i)=2\nu(x_i)-1.
\end{aligned}
\tag{ER.39}
$$

It also performs one startup source graft, two warm-up source
substitutions, $k$ acquired ternary choices and $k$ subsequent source
commits. Preparing the startup $a_0$ uses two fresh known $\alpha$
occurrences and one known pairing. A sufficient preparation of every
later $c$ is a fresh known $\alpha$ followed by two separately charged
known-constant substitutions. Each command graft consumes that copy.
These preparations are additional to operations on the unknown-source
register.

In an eager occurrence-tree representation a $c$ graft adds four source
nodes, and a substitution visits the old tree and increases its node
count by twice its old number of $\beta$ leaves. In particular

$$
\begin{aligned}
N(\rho^2(j(u)))&=4A(u)+6B(u)+7,\\
N(\rho^2(\iota(u)))&=4A(u)+6B(u)+9.
\end{aligned}
\tag{ER.40}
$$

For each fixed seed $u$, the $3^k$ words of length $k$ give $3^k$
distinct attained source supports. Thus the source retains unbounded
command information; eliminating a supplementary entry or order argument
does not imply bounded total memory.

Proof. The stationary producer gives one actual Read at each node of
each visited version. The only source traversals in this schedule are
the initial one and the $k+1$ refreshes; the local $LL$ lookups read
the acquired tables. This proves the first two equations, counting
repeated addresses on different versions as distinct actual calls.
The two leaf codes under $\rho^2$ have respectively two and three
leaves, so $\lambda(\rho^2(x))=2A(x)+3B(x)$.
The full binary-tree node identity gives the rest of (ER.39).
Each acquired command drives its one actual commit, giving the stated
source-operation counts.

The tree $c$ has three nodes and needs one attachment root, giving
four new source nodes. Substitution changes an old $\beta$ leaf into
a three-node pair and changes an old $\alpha$ only to a leaf.
Hence its node increase is $2B$; the traversal of old occurrences is
an explicitly chosen eager recipe, not a lower bound on every primitive.
The logical initializer $j$ adds two $\alpha$ leaves, whereas $\iota$
adds one $\alpha$ and one $\beta$. Applying the preceding leaf-code
identity proves (ER.40). This two-node source-material difference is
not a total implementation-cost comparison.
Finally Theorem 9.8 separates all the words for a fixed $u$, proving
the support count. Encoding this family by fixed-width bits would
require at least $\lceil k\log_2 3\rceil$ bits. $\square$

The account also charges the actual source installation and supply,
constant carriers, root attachments, code, input handling, address
emission, traversal stacks, tables, protocol records, output frames,
old material retained during replacement and all simultaneous copies.
Local lookup, parsing, replay on descriptions and serialization consume
additional finite work and storage. The producer has two local
combination/switch steps per branch; recording and the chosen table
receiver add their own work. No constant-time lookup or decoder tariff
is assumed. Equation (ER.39) counts raw literal calls and submitted
letters on this one run; it is neither a total fee formula nor an
optimality theorem. Pointwise finite termination gives no uniform
finite workspace bound over all seeds and words.

**Open problem 9.15 (ingress, source-busy and returned-use domains).**
Extend the independently meaningful expressions through actual unfinished
input, source and refresh operations, or establish a source-specific
obstruction for a stated finer interface. The existing acquired-input
fiber principle of [AIF, §§4–5][ERAIF] already requires a live distinction
here: fix one completed cut and independently supply any of the three
symbols. Before its source effect the current source, and hence $S$
and $B$, is identical in these three cases, while the acquired command
differs. A sufficient supplement for that command must therefore take
at least three values on this fiber. This is credited supplier
application, not a new binary pending-bit theorem.

Theorem 9.13 does not give individual task kernels or view transport
through pending input, source-operation internals, partial refresh,
table replacement or partial output. Extending it requires an actual
source/control realization retaining those distinctions, with its
legal inputs, full responses, successors and resource account.
The sparse binary all-cut proposal has different source, live-input,
reference, receipt and atomicity hypotheses and remains a separate
question; none of its all-cut assertions is imported here.

A mathematical decoder also does not install a service for arbitrary
historical-cut selection, authenticated view acquisition, publication,
cross-owner delivery or returned conversion. Those operations require
their own actual backing, ingress, rights and completed responses.
The present construction supplies actual initial/current acquisition
and retained owner-local use under Assumption 9.9; implementation below
its declared source primitives remains unproved.
Every original fixed-source, original-$Q$, unchanged-initialization,
parked-consumer and full-domain obligation retains its earlier scope.
In particular Open problem 8.1 for the original task and
[NCR, obligation 11.3(2)][ERNCR] are not settled by this new model.
The original $M_1(D)$, sharp $\lambda$, effective all-size certificates,
coherent infinite-source realization and the sustained four-expression
programme remain open. No physical spacetime interpretation, global
generator minimum, total-resource optimum or physical realization follows.

### 9.7 Supplier and novelty boundary

**Convention 9.16 (sources of the deduction).** The additional repository
references in this appendix designate their text at
$\texttt{3581743f15781df4f0db6bacedb6b7d637b9bb60}$;
Convention 7.1 continues to govern the preceding sections.
The new content is the concrete compound-tree image classification,
the one-graft entrance classification, their two distinct initializer
targets and the resulting source-only completed-cut application.
Backward determinism, finite ancestry parsing, shape decoding,
stationary acquisition, replay, task kernels and inverse-route algebra
are reused mechanisms. The deductions are ordinary mathematics, with
no new formal certificate or claim of worldwide priority.

| Supplier | Exact use and retained boundary |
| --- | --- |
| ER Theorem 3.1 and (ER.8)–(ER.9); §§5–6 | Effective substitution parsing and a strict descent measure; the earlier binary entry-height result, transported-constant collisions and omitted Read/failure histories are unchanged. |
| [PG, Definition 44.1 and Theorem 44.6][PG]; [Intrinsic Substitution Coordinates][ERISC], no-alpha and pair-image declarations and [owning exposition][ERISCB] | Paid prepared whole contexts, substitution injectivity and the exact image grammar. Fixed-context injectivity is not unknown-word recovery. Its intrinsic substitution root is a different notion from $\mathcal P$ and is not borrowed as an executable inverse. |
| [ABT, Theorem 12.1 and (ABT.39)][ERABT] | The exact effective two-step ordered shape code and its forward substitution correspondence. Equation (ER.33) additionally checks both actual grafts; no arbitrary-epoch inverse is inferred. |
| [Native Full Source Producer][ERPROD] and [owning exposition][ERPRODB] | One source-blind stationary traversal, exact original-node preorder, no repeated node and pointwise finite termination with unbounded finite workspace. The addressed table receiver and current local use are explicitly added paid work; no installed graft/input or arbitrary delivery follows. |
| [PG, Proposition 43.1][PG]; [SSA, Theorems 7.2–7.3][ERSSA]; [CSA, Theorem 6.3 and Corollary 6.4][ERCSA] | The two task-kernel inclusions and actual-image route/transition obligations. Their whole-storage observation and primitive-domain hypotheses are not identified with bare current-source support here. |
| [NCR, §§5–8 and 11.3][ERNCR]; [AIF, §§4–5][ERAIF] | Existing clocked/replay and acquired-input results, including the precommit fiber obstruction. The new word-separating menu and initializer do not extend their unchanged busy domains. |
| [Paid View Conversion, Assumptions 1.2 onward, Theorems 5.7 and 6.5][ERPVC] | An existing installed conversion/returned-use supplier under its own fixed-capacity entrance, installation, backing and authority contracts. Those stronger service hypotheses are not supplied by Theorem 9.13. |
| [Bennett][Bennett], transition-range criterion and history/copy/reverse construction; [Lanese–Phillips–Ulidowski, Definition 7.9 and Proposition 7.10][Lanese] | Classical backward uniqueness includes the command label; well-foundedness is a separate requirement. History retention, copying and reverse execution consume supplied resources. Their general mechanisms do not prove this tree partition or its entrance law. Causal equivalence allowing swaps/cancellation is not the literal finite-word target here. |

[ERABT]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md
[ERPROD]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean
[ERPRODB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs
[ERNSM]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean
[ERISC]: ../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean
[ERISCB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.scribe.cs
[ERNCR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md
[ERAIF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md
[ERSSA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md
[ERCSA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md
[ERPVC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md

## 追加锚（本行以下为增补区）

## 10. Marked partial substitution and an exact unfinished-source inverse

**Definition 10.1 (prefix substitution at an original leaf).** Retain
$\mathcal T,\rho,I,\delta,j,F_w$ from §§1, 3 and 9. Write
$E=\rho^2$, $A=E(\alpha)=\langle\beta,\alpha\rangle$ and
$B=E(\beta)=\langle A,\beta\rangle$; here $A,B$ are labelled trees,
whereas their shapes are the two codes of ABT Theorem 12.1. For a leaf
address $p$ of $x$, let $P_p(x)$ substitute exactly the original leaves
strictly before $p$ in left-first order. Newly created leaves are not
substituted again. Adjoin the end marker $\top$ and put
$P_\top(x)=\rho(x)$. Equivalently,

$$
\begin{aligned}
P_\varepsilon(\ell)&=\ell &&(\ell\in\{\alpha,\beta\}),\\
P_{Lq}(\langle s,t\rangle)&=\langle P_q(s),t\rangle,\\
P_{Rq}(\langle s,t\rangle)&=\langle\rho(s),P_q(t)\rangle.
\end{aligned}
\tag{ER.41}
$$

The mark is the next *original logical leaf*. In $E(P_p(x))$ its address
$p$ designates a whole code tile, not a terminal of the encoded tree.
It is not an elapsed epoch, a complete list of old leaf labels or an old
source snapshot.

Define a partial parser $D_p$ on finite labelled trees by

$$
\begin{aligned}
D_\top(z)&=\delta(z) &&(z\in I),\\
D_\varepsilon(z)&=z &&(z\text{ a leaf}),\\
D_{Lq}(\langle s,t\rangle)&=\langle D_q(s),t\rangle,\\
D_{Rq}(\langle s,t\rangle)&=\langle\delta(s),D_q(t)\rangle
                         &&(s\in I).
\end{aligned}
\tag{ER.42}
$$

An omitted case, or an undefined recursive call, rejects. In particular a
nonempty address requires a branch at each of its proper prefixes.

**Theorem 10.2 (exact partial-substitution image and geometric inverse).**
For every finite $x$ and every $p\in\operatorname{LeafPos}(x)\cup\{\top\}$,

$$
D_p(P_p(x))=x.
\tag{ER.43}
$$

For $p\ne\top$, $D_p(z)$ is defined exactly when $p$ is a leaf of $z$
and, at every right turn on the root-to-$p$ path, the entire left sibling
subtree belongs to $I$. When defined, $p$ is a leaf of $D_p(z)$ and
$P_p(D_p(z))=z$. For $p=\top$ its exact domain is $I$ and
$P_\top(D_\top(z))=z$. Thus

$$
(x,p)\longmapsto
 \bigl(\operatorname{Pos}(E(P_p(x))),p\bigr)
\tag{ER.44}
$$

is injective on the displayed marked domain, with a finite effective
inverse on its actual image. Replacing support by terminal boundary
preserves this assertion and the exact image test. No old table or
chronological record is an argument to either geometric inverse.

Proof. The inverse $\delta$ and its effective image grammar are the
suppliers of (ER.8). At $p=\top$ their two inverse identities give the
claim. At $p=\varepsilon$ the original and recovered objects must both be
leaves, and the claim is the identity. For $p=Lq$ both constructions
preserve the right child and recurse into the left. For $p=Rq$ the left
child has been wholly substituted, so apply $\delta\rho=\mathrm{id}$
there and the induction hypothesis on the right. This proves (ER.43).
Induction on the address proves the converse at the same time: each
right turn requires precisely the indicated $I$ test; no test is imposed
on an untouched right sibling. The induction also shows that the
recovered focus remains a leaf and that reapplying (ER.41) returns
exactly $z$. These are proved domain conditions, not an assumed inverse.

From the support in (ER.44), reconstruct the unlabelled finite shape and
apply the existing ABT two-step shape decoder to recover $P_p(x)$.
Apply (ER.42). Conversely, to recognize the marked image, first test the
ABT image grammar, then the stated path and $I$ conditions. Every
accepted pair is the encoding of its reconstructed $(x,p)$, by the two
inverse identities. A terminal antichain gives the same support by
prefix closure, proving its direction separately. All recursions are on
finite trees or proper address suffixes. $\square$

**Proposition 10.3 (phase and command do not replace the frontier).**
Even with the same pending command $\mathsf U$, the same update phase
and no previously completed command, the unmarked current encoded source
need not determine the acquired seed. Put

$$
 u=\langle\alpha,\alpha\rangle,\qquad
 v=\langle\beta,\alpha\rangle.
$$

Then $u\ne v$ but

$$
P_{RR}(j(u))
 =\langle\rho(a_0),\langle\beta,\alpha\rangle\rangle
 =P_{RL}(j(v)).
\tag{ER.45}
$$

Both marks occur before completion of a genuine left-first update of
that seed's $j$ entrance. Consequently even the *labelled* present
source, and hence its support and terminal boundary, collide at these
two unfinished cuts. Supplying the actual next-leaf mark restores the
inverse of Theorem 10.2 on the entire marked domain, not just this pair.

Proof. Both updates first substitute the two leaves of $a_0$. For $u$
the next substitution changes its left $\alpha$ to $\beta$ and leaves
frontier $RR$. For $v$ that substitution has not occurred, leaving
frontier $RL$ at its old $\beta$. Their right subtrees are therefore
identical as displayed. Encoding by the same $E$ preserves equality.
The old acquired tables differ at $RL$, so a task retaining those actual
tables distinguishes these cuts. The positive assertion is (ER.43).
This is a partial-source collision, distinct from the supplied AIF
pending-input-alphabet obstruction. $\square$

## 11. A finite controller with every declared unfinished primitive cut

**Assumption 11.1 (marked-cell controller model).** Fix one owner, source
occurrence, root port, ordered address system and finite program before
choosing the unknown finite seed $u$. The source initially contains $u$,
not a source-dependent program or supplied syntax table. Retain the paid
initial literal acquisition and the actual initializer $E(j(u))$ of
Construction 9.10. In particular its initial unknown-source traversal is
the stationary producer already cited there. Initial supply, known
$a_0$ preparation, attachment and two warm-up substitutions are actual
charged operations before the domain considered below.

Declare the following different continuing primitive basis. Data are
finite occurrence trees, backed finite address words, linked lists of
immutable addressed rows and finite latches. The control graph is finite;
these data carriers have no uniform finite size bound.

1. A literal source Read submits an actually backed original-root word
   and returns its truthful four-valued reply, preserving the current
   source. The continuing program has two fixed suffix variants: from
   its backed base address $q$, the instruction constructs the two word
   links for $LL$ or $RL$ before its query, as part of that same atomic
   occurrence, and retains their backing with its event. There are no
   separately observable suffix-construction substeps in this basis.
   These links, submitted letters and actual address traversal are charged.
2. A code-cell step at an acquired logical leaf address $p$, with its
   acquired old label $\ell$, tests the actual tile there and replaces
   $A$ by $B$ if $\ell=\alpha$, or $B$ by $\langle B,A\rangle$ if
   $\ell=\beta$. This is one atomic bounded source patch: at most five
   old tile nodes and nine new tile nodes. It reaches the tile along the
   actual supplied address and inspects each of its three or five old
   nodes to check the specified finite pattern. These positioning and
   pattern probes are charged source work, distinct from the literal
   Read opcode. Every incidence outside that tile is unchanged, except
   its attachment slot, which is retargeted to the new tile. Old tile
   material is retired and retained. No whole unknown subtree is copied.
   A guard mismatch is disabled; the
   construction must prove that it never occurs.
3. A known preparation constructs one fresh $A$ with its three known
   nodes. A graft attaches that prepared occurrence and the actual
   current source under one fresh root, on the specified left or right.
   These are separate primitives. There are no observable subassignments
   inside either declared atomic operation.
4. Local primitives inspect a row or a finite latch, take a fixed finite
   control edge, follow a backed list link, or allocate a fixed finite
   number of list/row/reference cells. Appending a row shares its already
   backed address word. Extending an address by $L$ or $R$ constructs one
   word link. A Read's receiver may append one row and at most two work
   addresses as its declared local coeffect. A row-transfer primitive
   constructs one new row/list cell referring to an already acquired
   address and label. It transfers no unbounded table in one occurrence.
   The fixed finite combinations printed as one row of Definition 11.3
   are the declared atomic instructions, with those local coeffects.
   No local coeffect scans a whole table or decodes an unknown subtree;
   root addressing retains its separately declared atomic convention.
5. A prescribed ingress receives one actual bit into a finite latch. A
   prescribed output sends one token from a fixed finite alphabet. Each
   primitive also updates the finite control and appends one actual
   event record, with references to its retained address/row backing.
   These references are not freely supplied contents. Their storage,
   traversal and any serialization are charged; one record does not
   mean one fixed-width physical bit.

The owner has exclusive authority to Read, patch, prepare and graft at
this port; to inspect and retain its local rows and latches; and to use
these input/output ports. Read traversals are source-stationary. No
other actor writes, reallocates, interrupts, supplies another request or
changes rights during a busy transaction. Allocation and retirement
follow fixed fresh sequential naming and append-only retention rules.
Thus retained old tiles, old tables, input records, event records and
emitted output all remain part of the actual joint state. None is an
independent source of choices. The fixed root/owner binding does not
encode $u$, a command word or a version count.

This is a declared mathematical primitive model, not a lowering to
NativeSerialMachine or PR57 tapes. Literal addressing and reference/list
operations have their stated word/reference operands. No unit physical
cost, bounded word width, hidden tape-level execution or free geometric
observation is inferred. Atomicity ends at the listed primitive cuts;
the finite protocol below exposes every such cut, including each
individual code-cell update, acquisition Read, row transfer and output
token.

**Definition 11.2 (actual table acquisition and retained data).** For a
logical tree $x$ write $\mathsf A(x)$ for its complete addressed literal
table in left-first preorder. It stores one row $(q,\ell)$ per actual
node; a lookup below a leaf returns $\mathsf{absent}$ by missing address.
Acquiring $\mathsf A(x)$ from an actual stationary $E(x)$ does not take
$x$ as a runtime argument. Start a work list $W=[\varepsilon]$ and an
empty row list $D$. At its head $q$, issue the two actual literal Reads

$$
qLL,\qquad qRL.
\tag{ER.46}
$$

Record both full replies; retain the first reply in a finite latch until
the second Read. Let a reply contribute 0 exactly when it is
$\mathsf{absent}$ and 1 otherwise. By ABT (ABT.34)/(ABT.37), the pairs
$00,10,11$ mean respectively logical $\alpha,\beta,\mathsf{branch}$.
Append the resulting row. Pop $q$ from $W$; in the branch case prepend
$qL,qR$, and otherwise append the acquired leaf-row reference to a
separate leaf list. Both operations use only the newly acquired replies
and already backed addresses. There is no independent source-size,
leaf-address or next-node selector.
The unused pair $01$ takes a fixed finite fault edge; that control has
no executing successor. The source-code invariant proved in Theorem
11.5 makes it unreachable, including during every refresh.

Denote the retained complete anchor table by $A_*$. Its role is
$\mathsf{live}$ or $\mathsf{held}$. A live anchor is bound to the present
source by $r=E(x)$ and $A_*=\mathsf A(x)$; a held anchor is authorized
retained data whose present-source binding is intentionally suspended.
The owner may inspect either role, but a held table is not advertised
as a fresh current-source result. Also retain the actual leaf-row list,
the new acquisition list $D$, its work list, a replacement list $C$,
row cursors and a local lookup-result latch. Scratch absent in a phase
is empty; when replaced, its old backing is retired canonically.

At startup acquire $\mathsf A(j(u))$ from the actual $E(j(u))$, make it
live, execute the local lookup and output recipe below, and reach the
first $\mathsf{Ready}$. The earlier initial traversal of $u$ remains in
the actual event record. No current table is inserted as advice.

**Definition 11.3 (complete continuing transition table).** Commands use
the prefix code

$$
\mathsf U=0,\qquad\mathsf L=10,\qquad\mathsf R=11.
\tag{ER.47}
$$

The following are all reached control families and all continuing
transitions; the unused decoder fault control has no successor.
An ingress row consumes exactly its stated bit. Every other row is one
$\mathsf{Advance}$ occurrence in the basis of Assumption 11.1. Addresses,
list heads and acquired replies are data fields, not infinitely many
program states. The command latch $a$ is retained through the transaction.

| Reached control | Enabled operation and actual successor |
| --- | --- |
| $\mathsf{Ready}$ | Supply 0 latches $\mathsf U$ and enters $\mathsf{Select}(\mathsf U)$; Supply 1 enters $\mathsf{Tail}$ with that acquired leading 1. |
| $\mathsf{Tail}$ | Supply 0 latches $\mathsf L$; Supply 1 latches $\mathsf R$; either enters $\mathsf{Select}(a)$. |
| $\mathsf{Select}(\mathsf U)$ | Mark $A_*$ held; point to the head $p$ of its retained leaf list and enter $\mathsf{Edit}(p)$. |
| $\mathsf{Select}(a)$, $a=\mathsf L,\mathsf R$ | Mark $A_*$ held; prepare a fresh $A$ and enter $\mathsf{Graft}(a)$. |
| $\mathsf{Edit}(p)$, $p\ne\top$ | Execute the guarded code-cell step using that leaf row's acquired old label. Advance to the next original leaf-row reference, or $\top$ if none; enter $\mathsf{Edit}$ at that mark. |
| $\mathsf{Edit}(\top)$ | Append the update-completion event, clear the refresh lists, set $W=[\varepsilon]$, and enter $\mathsf{Read0}(\mathsf U,\varepsilon)$. |
| $\mathsf{Graft}(a)$ | Consume the prepared $A$ in the corresponding whole graft. Clear the refresh lists, set $W=[\varepsilon]$, and enter $\mathsf{Read0}(a,\varepsilon)$. |
| $\mathsf{Read0}(a,q)$ | Read $qLL$, save its full reply $v$, and enter $\mathsf{Read1}(a,q,v)$. |
| $\mathsf{Read1}(a,q,v)$ | Read $qRL$ and perform exactly Definition 11.2's row/work/leaf-list update. If $W$ is now empty enter $\mathsf{Replace0}(a)$; otherwise enter $\mathsf{Read0}(a,\operatorname{head}W)$. |
| $\mathsf{Replace0}(a)$ | Allocate empty $C$, preserve the held anchor and complete $D$, and enter $\mathsf{Copy}(a,\varepsilon)$ at the first row of $D$. |
| $\mathsf{Copy}(a,q)$ | Transfer just that row of $D$ into $C$, including its leaf-list link when it is a leaf. Advance to the next row; after the last row enter $\mathsf{Bind}(a)$. |
| $\mathsf{Bind}(a)$ | Retire the old anchor and its leaf list. Make $C$ and its leaf list the new live anchor; retain $D$ in retired backing; enter $\mathsf{Lookup}(a,\varepsilon)$. |
| $\mathsf{Lookup}(a,q)$, $q\ne\top$ | Inspect just that acquired anchor row. If $q=LL$, save its literal reply and enter $\mathsf{OutStart}(a)$; otherwise move to the next row, or $\top$, in $\mathsf{Lookup}$. |
| $\mathsf{Lookup}(a,\top)$ | Save $\mathsf{absent}$ and enter $\mathsf{OutStart}(a)$. |
| $\mathsf{OutStart}(a)$ | Send $\mathsf{start}$ and enter $\mathsf{OutRow}(a,\varepsilon)$. |
| $\mathsf{OutRow}(a,q)$ | Send that anchor row's one reply token and advance its actual row cursor; after the last row enter $\mathsf{OutSep}(a)$. |
| $\mathsf{OutSep}(a)$ | Send $\mathsf{sep}$ and enter $\mathsf{OutResult}(a)$. |
| $\mathsf{OutResult}(a)$ | Send the retained local lookup result and enter $\mathsf{OutEnd}(a)$. |
| $\mathsf{OutEnd}(a)$ | Send $\mathsf{end}$ and enter $\mathsf{Finish}(a)$. |
| $\mathsf{Finish}(a)$ | Retire remaining active scratch, clear the command/reply/result latches and return to $\mathsf{Ready}$. |

An $\mathsf{Edit}$ control has implicit command $\mathsf U$.
$\mathsf{Read1}$ carries its actual first reply; all other stale reply
latches are cleared. The result latch is empty until lookup finishes,
and is cleared by Finish. Traversal work-list tails, copied prefixes
and output prefixes are actual retained objects; they are not additional
inputs. Startup uses the same lookup/output rows with a fixed startup
tag in place of $a$, before the first Ready.

Every event records its opcode, actually supplied/emitted token or
actual literal reply, and references to operands used. Control edges
and row transfers also have distinct event tags. These records form
$\Gamma$; the emitted tokens form $\mathsf{Out}$. A complete frame has
$\mathsf{start}$, the preorder word of logical node replies,
$\mathsf{sep}$, the local $LL$ reply and $\mathsf{end}$. The preorder
word reconstructs the entire logical tree and its addressed table by the
ordinary full-binary-tree parser. Partial frames remain partial; no end
marker or completed response is assumed before its actual emission.

**Definition 11.4 (receipt, full domain and primitive task).** The
current receipt $f$ consists precisely of the control family and the data
printed in its control notation in Definition 11.3. Thus it has a finite
phase tag, at most one command, one addressed frontier/row cursor, and
one finite first-reply latch. Ready and Tail have only their respective
finite tags. Addresses denote actual backed references at the indicated
roles; $\top$ is the fixed end token. No epoch, global primitive ordinal,
seed, completed command word, archive index, table or event transcript
is an additional field of $f$. Its finite tags/latches and reference
binding are actual controller material updated by the same transitions.
The selected address observation is its backed $L/R$ word, not an
allocation number or the name of a cell containing that word. Equality
of an observed table likewise compares its addressed contents and fixed
owner/port binding, not row-allocation names. Actual reference identities
remain in $J$ and are reconstructed by canonical replay; they are not
hidden clock fields of the selected receipt. Reading or transmitting
the word through its backing is additional charged work.
The role of $A_*$ is determined by the phase: live before Select executes
and from Lookup onward; held from Edit/Graft through Bind.

Let $\mathcal H_\partial$ be *all* finite lawful executed primitive
prefixes beginning at a seed's first Ready, for every finite
$u\in\mathcal T$ and every finite supplied bit word extendible under
(ER.47). It includes the empty prefix, the unfinished leading 1, selected
but unapplied commands, every Edit frontier including $\top$, prepared
but unattached constants, both Reads at every refresh node, every
partially copied replacement list, before and after binding, each local
lookup position, each partial output and Finish. There are no other
continuing primitives in this declared model. An unfinished prefix need
not have received all of its eventual command. An extension beyond its
next input is not fixed in advance.

Before defining any view, specify the task $Q_\partial$. Its present
readout is the authorized retained anchor table, its live/held role and
the current controller receipt. This is already acquired finite
material, not an oracle for an unread current table. Its experimental
actions are Supply(0), Supply(1) and Advance, enabled exactly by the
transition table. At an input phase both bits are admitted; elsewhere
only Advance is enabled. A disabled trial returns the fixed $\mathsf{none}$
and makes no executing successor or record append. A legal action's
complete response consists of its action identity, legal/success type,
actual Read reply or emitted token when present, actual
$\Delta\Gamma,\Delta\mathsf{Out}$, and its complete original joint
successor $J'$. That successor includes the source occurrences, all
retired material and records, actual tables, buffers, latches, reference
backing, control, bindings and rights. It is a mathematical coordinate
of the response, not a transmitted snapshot or an added read port.
Finite legal continuations compose these responses. Task equivalence
requires equal present readouts and equal partial response maps,
including domains and the fixed disabled-trial behavior.

**Theorem 11.5 (actual acquisition, partial updates and unique cut form).**
Assumptions 11.1 and Definitions 11.2–11.4 give one finite program,
independent of seed and future input, with the following properties on
all of $\mathcal H_\partial$.

At a Ready cut after completed transactions $w$, put $x=F_w(j(u))$.
The actual source is $E(x)$ and its live anchor is $\mathsf A(x)$,
acquired from that source by (ER.46). During a transaction $a$:

- Tail, Select and Graft retain source $E(x)$ and anchor $\mathsf A(x)$;
- at Edit($p$) the source is exactly $E(P_p(x))$ and the held anchor
  remains $\mathsf A(x)$;
- from Read0 through Bind the source is $E(y)$, $y=F_a(x)$, and the
  held anchor remains $\mathsf A(x)$;
- from Lookup through Finish the source is $E(y)$ and the live anchor
  is precisely the newly acquired $\mathsf A(y)$.

Every code-cell guard succeeds and no decoder fault is reached. The
refresh queries address the actual
same source occurrence and acquire each logical node exactly once with
two Reads. Replacement and lookup terminate, and the lookup uses only
the retained acquired anchor, making no source Read. Every finite
command transaction terminates when its finitely many prescribed
Advances are supplied. No uniform bound over seeds or words is implied.

Every reached cut has a unique form $(u,w,f)$, with $w$ counting
*finished transactions*, and that form determines the entire actual
primitive prefix and complete $J$. Each of the following separately
recovers that form effectively on its actual image:

$$
\bigl(\operatorname{Pos}(r),f\bigr),\quad
\bigl(\operatorname{LeafPos}(r),f\bigr),\quad
\bigl(A_*,\operatorname{role}(A_*),f\bigr),\quad
\Gamma.
\tag{ER.48}
$$

Proof. At a stationary $E(x)$, the two existence bits in (ER.46)
classify a reached logical node by ABT.34. If it is a branch, both
children are actual logical nodes; otherwise there are no logical
children to schedule. The work-list induction says that $D$ is exactly
the logical preorder prefix already visited and $W$ the pending
preorder frontier. Thus each logical node is visited exactly once and
the final $D$ and leaf list are $\mathsf A(x)$ and its true leaf rows.
Finiteness of $x$ proves termination. This proves startup acquisition
without supplying the runtime with the unknown $x$.

Suppose the Ready invariant holds. The actual input code selects just
one $a$. For $\mathsf U$, the retained old leaf list supplies precisely
the original leaves of $x$, their actual addresses and acquired labels.
Different original leaves are incomparable by prefix. Rewriting one
tile therefore leaves every remaining original leaf tile at its old
address and preserves all old logical branch positions. Its guard is
exactly the acquired $A/B$
pattern, so it succeeds. Pairing preservation gives, after each step,
$E(P_p(x))$ at the next listed frontier. At $\top$ this is
$E(\rho x)$. In particular a new logical leaf created below a rewritten
old leaf never enters the old leaf list. A graft uses its actual prepared
$A=E(\alpha)$ and preserves the actual old source as its other child,
so its result is $E(F_a(x))$. All constants and new patch nodes are
known material; the old source is neither guessed nor freely copied.

The stationary acquisition induction applies again to $y=F_a(x)$.
During replacement $C$ is exactly the prefix of the acquired $D$ already
transferred, while the held anchor remains readable. After the last
transfer, Bind makes that same complete acquired value live at the
same source port; no unacquired candidate is activated. Lookup examines
successive actual rows until $LL$ is found or the list ends. Its saved
reply is therefore the exact logical literal at $LL$, including
absence, using no fresh source access. Output consumes exactly those
rows and that saved reply. All lists are finite. Finish restores the
Ready invariant with $wa$ in place of $w$. Induction proves all stated
source/table invariants, actual acquisition, rights preservation and
progress. Source-stationarity holds because no update is enabled during
Read0 through Finish.

For the cut form, first $u,w,f$ determines a cut as follows. Run the
canonical startup on the *description* $u$, the complete transactions
of $w$, and the indicated current transaction. Its input prefix is
fixed by f: none at Ready, the single 1 at Tail, and the unique complete
code of $a$ at other busy phases. Each local phase position is unique
within that transaction: Edit consumes different old leaf-row
references, the two refresh subphases visit each different node once,
Copy and output each advance a row cursor once, and Lookup never
returns to a row. All other phases occur once. The first-reply latch is
fixed by its actual query. Hence the specified phase and cursor are
reached exactly once, reconstructing buffers, retired objects, canonical
allocation names, rights, $\Gamma$ and $\mathsf{Out}$ as well as source
and anchor. This is descriptive replay of recovered data; no replay
port or resetting of the actual source is used.

It remains to prove that the four data in (ER.48) recover this form,
rather than assume its inverse. For support, ABT decodes the current
logical tree $z$. At Ready, Tail, Select or Graft it is $x$; apply
Theorems 9.3 and 9.5 to recover exactly $u,w$. At Edit($p$), first apply
Theorem 10.2 to obtain $x=D_p(z)$, then the same ancestry parser. At all
later phases $z=y=F_{wa}(j(u))$; the ancestry parser gives $u,wa$, and
the pending command in $f$ identifies its last letter. Removing that
one letter gives $w$. These are necessary checks on the actual image,
not an assumed predecessor relation. The receipt supplies the attained
local phase. Terminal boundary first gives support by prefix closure,
so its decoder has the same conclusion.

For the memory datum, the actual complete anchor reconstructs its
logical labelled tree directly. Before Bind executes it is $x$, so the
ancestry parser gives $u,w$. After Bind executes it is $y$, so it gives
$u,wa$ and the pending final letter is removed. Ready and Tail use $x$.
With these data, the forward construction computes every partial source
and workspace field; it need not Read or invert an unknown physical
source. The role and phase determine the correct case even while $C$
is only a prefix or while a newly acquired $D$ already exists.

Finally, $\Gamma$ contains the actual initial producer replies and
addresses, which reconstruct $u$, as well as every subsequently
supplied bit and every executed transition tag. Replay from the common
initialized program through precisely this finite occurrence word gives
the reached phase, the finished commands and the full state. No
endpoint snapshot is appended to this temporal datum. Each decoder
therefore gives the same actual $(u,w,f)$, and equality of that form
implies equality of the primitive prefix by uniqueness just proved.
$\square$

## 12. Four individual task kernels, lawful transport and same-run costs

**Definition 12.1 (four expressions of this actual protocol).** All four
expressions are projections of the single reached joint process above:

$$
\begin{aligned}
S_\partial(h)&=(\operatorname{Pos}(r(h)),f(h)),\\
B_\partial(h)&=(\operatorname{LeafPos}(r(h)),f(h)),\\
T_\partial(h)&=\Gamma(h),\\
M_\partial(h)&=(A_*(h),\operatorname{role}(A_*(h)),f(h)).
\end{aligned}
\tag{ER.49}
$$

$S_\partial$ observes the actual current source's ordered incidence
support and its actual controller receipt. $B_\partial$ observes where
that current source terminates, together with the same receipt and its
marked address binding. Neither observes workspace geometry, old table
payloads, retired tiles or the event archive. Their extra control
observation is explicit: these are not §9's bare source views during
busy phases. A mark need not be an encoded terminal address.
$T_\partial$ is actual occurrence order, including ingress, queries,
updates, local work and outputs; it is not elapsed physical duration or
a freely chosen clock coordinate. $M_\partial$ is the one actual
acquired anchor and its local authority/role/control record, including
when the anchor is held during refresh. It contains neither a past-table
archive nor $\Gamma$ as an extra payload. Its use in lookup/output is
part of the actual controller, rather than only a symbolic decoder.

All fixed owner/port/permission fields are implicit equal comparison
fields. Giving a mathematical view value does not transfer those rights
to another owner. The owner can obtain spatial/boundary descriptions
from an acquired table at stationary refresh completion by forward
encoding and label erasure. During Edit it can compute the same finite
descriptions from its held acquired table and actual frontier using
(ER.41). Such computation and delivery consume local work, address
backing and output storage; no instantaneous free view-acquisition
service is added to the primitive task.

**Theorem 12.2 (four exact kernels at every declared primitive cut).**
For every $h,k\in\mathcal H_\partial$ and for each individual
$V\in\{S_\partial,B_\partial,T_\partial,M_\partial\}$,

$$
 V(h)=V(k)
 \quad\Longleftrightarrow\quad h=k
 \quad\Longleftrightarrow\quad h\sim_{Q_\partial}k.
\tag{ER.50}
$$

All twelve effective same-cut recoveries on the actual view images are
mutual inverses and agree along every route. They preserve the entire
lawful partial response map and the complete original successor of
this controller at *each* primitive, including ingress and every
unfinished update, refresh, replacement, lookup and output position.
They also preserve every finite lawful adaptive continuation.

Proof. Here equality of histories includes the seed and executed prefix
from its first Ready. Theorem 11.5 proves separately that equality of
each of the four view data recovers exactly that history; each view is
also a function of that history. Thus every individual view has the
diagonal kernel, without taking an intersection of kernels.

Check both task-kernel directions for each view. Equal $S_\partial$
gives the same seed, finished word and local receipt by its partial-source
parser, hence the same complete state and every future response.
Conversely task equivalence includes equal actually acquired anchor,
role and receipt; its memory decoder gives the same history and
therefore the same present source support and receipt. Equal
$B_\partial$ gives the same history via prefix closure and that parser,
hence the same responses; task equivalence gives the same recovered
history and consequently the same terminal antichain and marked
receipt. Equal $T_\partial$ gives the same actual seed acquisition and
primitive prefix through replay, hence the same responses; task
equivalence gives the same anchor/receipt, whose decoder fixes the
unique actual chronology including startup. Equal $M_\partial$ gives
the same history by the acquired-table decoder and hence the same
responses; task equivalence directly includes equality of this actual
retained readout. This proves both inclusions separately for all four.
The reverse directions do not use a hidden successor coordinate to
separate cuts: the task's already acquired present readout suffices.

Write $d_V(V(h))=h$ for these actual-image decoders. Set
$R_{VW}=W\circ d_V$. Then, on the attained images,

$$
R_{WV}R_{VW}=\operatorname{id},\qquad
R_{WZ}R_{VW}=R_{VZ}.
\tag{ER.51}
$$

Both compositions decode and re-encode the same actual cut. For an
action $b\in\{\operatorname{Supply}(0),\operatorname{Supply}(1),
\mathsf{Advance}\}$, let $A_b^V$ be its induced partial view successor.
Its domain is exactly the view of the enabled controls in Definition
11.3, not all mathematical view values or all physical operations.
The common decoded receipt determines that domain. For each enabled
case the transition table and Theorem 11.5 give the same actually
executed operation, literal reply, output token, record append and full
original $J'$; the resulting cut is again in $\mathcal H_\partial$.
Therefore, including equality of domains,

$$
 R_{VW}A_b^V=A_b^W R_{VW},\qquad
 \operatorname{Resp}_b^W R_{VW}=\operatorname{Resp}_b^V.
\tag{ER.52}
$$

For disabled trials both sides return the same $\mathsf{none}$ without
execution. Thus (ER.52) includes lawful full-response/successor
compatibility, rather than merely tree conjugacy. Induction proves it
for finite continuations. For finite adaptive experiments, equal acquired
responses select the same next branch at every stage, so the same
induction applies. These are algorithms on finite acquired descriptions;
the theorem does not install arbitrary-owner or historical-cut conversion.
$\square$

**Proposition 12.3 (same-run operation and material account).** Put
$x_i=F_{a_1\cdots a_i}(j(u))$, $0\le i\le k$, and
$N(x)=2\lambda(x)-1$. For the actual run from installed $u$ through
$k$ finished commands, including initial acquisition, the exact literal
Read count and submitted-letter count are

$$
\begin{aligned}
N_{\rm Read}
 &=N(u)+2\sum_{i=0}^k N(x_i),\\
L_{\rm addr}
 &=\sum_{q\in\operatorname{Pos}(u)}|q|
   +\sum_{i=0}^k\left(
        2\sum_{q\in\operatorname{Pos}(x_i)}|q|+4N(x_i)\right).
\end{aligned}
\tag{ER.53}
$$

Let $\ell(y)$ be the one-based preorder row rank of $LL$ in
$\mathsf A(y)$ when present, and $N(y)+1$ when absent. It counts exactly
the local lookup occurrences. For one continuing transaction $a$ from
$x$ to $y=F_a(x)$, its exact number of declared primitives is

$$
 |\operatorname{code}(a)|+9+4N(y)+\ell(y)
       +\boldsymbol 1_{a=\mathsf U}\lambda(x).
\tag{ER.54}
$$

It transfers $N(y)$ replacement rows and sends $N(y)+4$ output tokens.
A U transaction performs precisely $\lambda(x)$ bounded source patches,
allocating $5A(x)+9B(x)$ new active-tile nodes over the transaction and
retiring $3A(x)+5B(x)$ old tile nodes. A graft prepares three known
nodes and allocates one attachment root. Here $A(x),B(x)$ denote alpha
and beta leaf counts, not the constant tiles $A,B$. Each logical refresh
constructs $4N(y)$ query-suffix word links and $N(y)-1$ child-address
links. The selected extensional receipt has at most $h(r)+c$ symbols
for one fixed constant $c$ independent of seed and command word.
These subtotals are not a physical fee or peak-storage optimum.

Proof. Startup's raw source producer visits each node of $u$ once.
Every logical refresh, including $x_0$, visits every logical node twice
by (ER.46), with addresses of length $|q|+2$. No patch, retained lookup,
row copy or output issues an additional source Read. This gives both
identities in (ER.53) on the same run, counting repeated queries on
different versions as different calls.

A continuing transaction receives one bit for U or two for a graft.
It has one Select step, either its $\lambda(x)$ cell steps followed by
one Edit($\top$) step or one Graft step, $2N(y)$ refresh steps, one
Replace0, $N(y)$ Copy steps, one Bind, $\ell(y)$ Lookup steps,
$N(y)+4$ output steps, and one Finish. Collecting these terms gives
(ER.54). A logical alpha tile has three nodes and its new B has five;
a logical beta tile has five and its new pair of B and A has nine.
Every original logical leaf is used once, proving the material counts.
The tile guards additionally inspect exactly $3A(x)+5B(x)$ old tile
nodes, with submitted tile-address length
$\sum_{p\in\operatorname{LeafPos}(x)}|p|$; these probes are not counted
as literal Read opcodes in (ER.53). Each of the $2N(y)$ queries makes
two fresh suffix links. Each logical branch makes two child-address
links, and a full binary tree has $N(y)-1$ child incidences. Finally the
receipt has fixed-width finite tags and at most one word for an actual
logical source position; that position is also a position of $r$.
Its word length is at most $h(r)$. This bounds its selected extensional
description, not the physical width of reference names or their backing.
No unknown source-node copy is hidden in those replacements. $\square$

**Definition 12.4 (additional resources and scope of parsimony).** The
operation counts also require the actual source/owner/program
installation, initial $a_0$ carrier, warm-up substitutions, finite input
latches, reference backing, work/leaf lists, old and new addressed rows,
the simultaneous held anchor, complete refresh list and replacement
prefix, retired source tiles/tables/scratch, $\Gamma$, output retention
and its serialization. Every occurrence's record and all referenced
material remain charged. A code-cell step with a long address is not a
constant-time root-to-cell seek. Table sharing saves a specified copy
of an address value; it does not erase the address's backing, its
reference representation or later traversal cost. Decoding shape,
parsing (ER.42), ancestry inversion and descriptive replay are finite
additional local computations whenever requested, not free runtime
oracles used by the controller.

The chosen task justifies the resources as follows. The inherited
$E$ code makes erased geometry literal-informative; its fixed-depth
minimality is ABT's supplied result, not a new minimum. The inherited
$j$ entrance identifies the actual entry among ternary ancestors; the
precise zero/one-graft comparison remains only Corollary 9.5's scope.
The U and two oriented graft commands are the stipulated three-way
continuation menu. No reduction to a globally indispensable alphabet is
asserted. Acquired input/control distinctions are necessary on the
unchanged-source ingress fiber by AIF; (ER.45) additionally shows that
pending command and update phase alone fail on actual partial sources.
Read subphase and row/output position distinguish actual unfinished
work while source geometry is stationary. The displayed receipt is a
sufficient implemented record of those positions; no least receipt
alphabet or least pointer representation is claimed.

The anchor is acquired by actual queries, supplies each cell operand,
and is actually called by lookup/output; acquisition and retained use
are different proved parts of Theorem 11.5. Source binding and write/read
rights come from the fixed owner's declared exclusive capabilities,
not from a view isomorphism. The chronological record is actual charged
backing for occurrence order and the full successor; geometric recovery
does not make that retained material free. Descriptive replay recovers
it without including it as a second payload in S, B or M. By Theorem
9.8, even completed sources for a fixed seed separate $3^k$ command
words, so neither a finite control graph nor the bounded size of an
individual tile step implies bounded total memory.

**Convention 12.5 (supplier and novelty boundary).**
References to the repository in §§10–12 use their text at
$\texttt{52dbcd87147da56ebc64a90fb2801651f39d1be4}$.
The source-specific addition is the exact contextual image and inverse
(ER.41)–(ER.44), the collision (ER.45) within actual one-graft entrances,
and their integration with the complete declared protocol. The protocol
retains an old acquired anchor across every cell update, refresh and
partial replacement and replaces it only after genuine acquisition.
Consequently every declared continuing primitive cut, rather than only
an active-source contour or completed cut, has the four *individual*
task kernels of (ER.50). This is repo-derived mathematical synthesis,
without a new Lean certificate or a claim of worldwide priority.

ER Theorems 9.3/9.5/9.8 supply ternary ancestry and stable source shape
recovery. ABT Theorem 12.1 and its two-query decoder supply $E$'s grammar
and stationary acquisition bits. IntrinsicSubstitutionCoordinates's
`no_alpha`, `pair_image`, private `substitution_injective` and owning
exposition supply the substitution-image facts; the private proof is not
being presented as a new accessible API. NativeFullSourceProducer's
`native_source_producer` and its private traversal/Read/stationarity
proofs supply the initial stationary producer, under its unbounded
finite-workspace contract. None of those results states the marked
partial-source image criterion or supplies this continuing controller.

AIF Theorem 4.4 supplies all-cut deterministic replay with its acquired
seed, consumed input and primitive ordinal. SSA/CSA/PVC supply exact
four-view/returned-use results under their respective whole-storage,
atomic patch, install and authority hypotheses. Their route algebra and
both task-kernel inclusions are reused here. S and B here exclude
workspace, old tables and the event archive; they include the explicitly
constructed local receipt instead of observing whole storage. The
source-specific partial inverse, not replay alone, closes their busy
source-to-anchor direction. SSA §13's restricted relocation data paths
do not construct these cell rules or this global controller. PR57 keeps
its candidate-array source unavailable during writeback and its own
restricted busy observation menu. Here the encoded source remains an
actual full tree at every bounded tile cut, and the controller receipt
and logical acquisition interface are different declared observations.
No native/PR57 source-byte or fine-relocation implementation is inferred.

Huet, *The Zipper*, JFP 7(5), 549–554, [author manuscript, §§1.1–1.3](https://pauillac.inria.fr/~huet/PUBLIC/zip.pdf),
is a literature-attested supplier for focus/context decomposition and
local editing. Its focus contains a subtree and retained sibling
context; it does not supply (ER.42)'s reconstruction of the substituted
siblings from this current erased source and a next-leaf address.
Bennett's [history/copy/reverse construction][Bennett] is the
literature-attested replay/reversibility comparison: record storage and
copy/reverse work are additional resources. Neither supplier proves
(ER.45) or this common-source acquisition/busy-cut correspondence.
The exact tree-image deductions and protocol proofs above do not rely
on absence of a search hit as evidence of novelty.

**Definition 12.6 (unchanged claims and remaining domains).** This
controller changes ER §9's continuing primitive and observation/task
interfaces: whole U is refined into the specified acquired-leaf code
patches; the known three-node graft constant has its own bounded
constructor; ingress has two actual bit sites; refresh acquires a *logical*
table by two literal queries per logical node; replacement transfers
one acquired row at a time; output is the specified logical preorder
frame; and space/boundary additionally expose the current controller
receipt. At completed cuts the physical source is the same
$E(F_w(j(u)))$, and logical disclosure determines its complete literal
source table by forward encoding. The full joint successors, output
frames and busy readouts nevertheless belong to this newly defined
$Q_\partial$, not ER.35 or the original prediction task ER.3.

Theorem 12.2 covers the entire post-first-Ready primitive domain of this
explicit model; it does not cover finer cuts inside its atomic source
Read, bounded patch, list/reference coeffect or Bind, arbitrary busy
interrupts, independent requests or other owners. Initial acquisition
is actually performed, but no four-kernel theorem for pre-first-Ready
startup is asserted. Callable use is the owner's current retained
lookup/output routine. Arbitrary historical-cut selection, authenticated
cross-owner acquisition, installed conversion/delivery and physical
lowering remain separate obligations. None is obtained by merely
running a mathematical decoder on a view description.

Every prior fixed-$G_{gc}$, original-$Q$, unchanged-initialization,
parked-consumer and original-authority obligation keeps its precise
scope, including Open problem 8.1 and NCR 11.3(2). The original
$M_1(D)$, sharp $\lambda$, effective all-size certificates, coherent
infinite-source realization, general resource minima and the sustained
space/time/boundary/memory programme remain unresolved. These bounded
finite-source recovery results supply no physical spacetime identity,
universal alpha/beta reduction or completion of that programme.

## 追加锚（本行以下为增补区）

## 13. Exact source fibres in the first acquired update

**Definition 13.1 (first-U cuts and admissible frontiers).** Retain exactly
Assumptions 11.1 and Definitions 11.2–11.4, including the actual initial
acquisition of $u$, the initialization $E(j(u))$, the acquisition of its
logical anchor and the first Ready. For each finite seed $u$, supply the
single bit 0 there, execute Select, and execute an initial segment of the
prescribed leaf-cell steps. Denote the resulting Edit cut by $e(u,p)$,
where $p$ is the next original leaf of $j(u)$, or $\top$ after the last
cell step. Thus

$$
\begin{aligned}
\mathcal E_1
 &=\{e(u,p):u\in\mathcal T,
       p\in\operatorname{LeafPos}(j(u))\cup\{\top\}\},\\
z(e(u,p))&=P_p(j(u)),\qquad r(e(u,p))=E(z(e(u,p))),\\
A_*(e(u,p))&=\mathsf A(j(u)),\qquad
\operatorname{role}(A_*)=\mathsf{held}.
\end{aligned}
\tag{ER.55}
$$

The seed and mark determine an actual prefix by Theorem 11.5. No later
command, refresh or output of this U transaction has occurred. The end
mark is still an Edit cut: the completion-record step is its next Advance.
This is a subdomain of $\mathcal H_\partial$, with the same owner, actual
source port, initializer, program and task $Q_\partial$.

For a finite labelled tree $v$, let $\mathcal L_I(v)$ be the leaves $q$
of $v$ such that, at each right turn on the root-to-$q$ path, its entire
left sibling subtree lies in $I$. This is the domain test of Theorem
10.2; in particular $D_q(v)$ is defined for exactly these leaves.
Put

$$
\begin{aligned}
b_0&=\langle\alpha,\alpha\rangle=a_0,&
b_1&=\langle\beta,\alpha\rangle,&
b_2&=\langle\beta,\beta\rangle=\rho(a_0),\\
\mathfrak F(z)
 &=\{(u,p):e(u,p)\in\mathcal E_1,\ P_p(j(u))=z\},&
m(z)&=|\mathfrak F(z)|.
\end{aligned}
\tag{ER.56}
$$

These are fibres of the decoded *current source*, with its frontier
forgotten in the observation. The actual controller and its receipt
have not been modified. Ordered source support, terminal boundary and
labelled source have the same fibres on this domain, by ABT Theorem
12.1 and prefix closure. All comparisons use the fixed original root
and orientation. Equality here is of source-tree contents; it does not
identify the complete occurrence, allocation or archive fields of $J$.

**Theorem 13.2 (exhaustive first-U ambiguity and actual separation).**
For every $z\in\mathcal T$, the following disjoint cases give its entire
fibre:

$$
\mathfrak F(z)=
\begin{cases}
\{(v,LL)\},&z=\langle b_0,v\rangle,\\
\{(v,LR)\},&z=\langle b_1,v\rangle,\\
\{(D_q(v),Rq):q\in\mathcal L_I(v)\}
 \ \cup\ \{(\delta(v),\top):v\in I\},
       &z=\langle b_2,v\rangle,\\
\varnothing,&\text{otherwise}.
\end{cases}
\tag{ER.57}
$$

The conditional singleton in the third case is empty when $v\notin I$.
In particular that case has the exact size

$$
m(\langle b_2,v\rangle)
 =|\mathcal L_I(v)|+\boldsymbol 1_{v\in I}
 \le\lambda(v)+1.
\tag{ER.58}
$$

Every displayed member is attained by the existing controller, and the
finite fibre and its corresponding actual held anchors can be recovered
from the current source description. Distinct members of any one fibre
have different actually acquired anchors. Furthermore their *next enabled
Advance operations* have pairwise different current-source successors,
including the $\top$ case. Consequently they are pairwise inequivalent
for the unchanged $Q_\partial$, both by its present acquired readout and
by its actual next complete response.

Proof. The first two leaves of every $j(u)$ are $LL,LR$. At $LL$ no
cell has changed and its left subtree is $b_0$. At $LR$ just its first
alpha cell has changed, giving left subtree $b_1$. Once both have
changed, the left subtree is $b_2$. For a later leaf $Rq$, (ER.41) gives

$$
 P_{Rq}(j(u))=\langle b_2,P_q(u)\rangle,
 \qquad P_\top(j(u))=\langle b_2,\rho(u)\rangle.
\tag{ER.59}
$$

The three left subtrees are different. In the third case Theorem 10.2
says precisely that $P_q(u)=v$ has a solution at an original leaf $q$
if and only if $q\in\mathcal L_I(v)$, and that its unique solution is
$u=D_q(v)$. For $\top$, the supplied exact image grammar gives precisely
$v\in I$ and $u=\delta(v)$. Conversely every such recovered $q$ is an
original leaf of the recovered $u$, and reapplying $P_q$ gives $v$.
The existing startup acquires this seed, and the leaf list reaches this
cut after finitely many lawful cell steps. This proves both exhaustion
and actual realization, including the first two cases. It also proves
(ER.58), since its nonterminal candidates are distinct leaves.

All tests and inverses used here terminate on finite syntax. The ABT
shape inverse first recovers $z$ from current support; boundary first
gives that support. Formula (ER.57) then enumerates all candidates and
computes each $\mathsf A(j(u))$. This is enumeration on a source
*description*, not an additional readout of the actual held slot.

Two different marks for the same seed cannot give the same source.
Indeed, moving from one original leaf to the next executes a nonempty
sequence of cell substitutions. On logical syntax each alpha cell raises
$\nu=2A+3B$ by 1, and each beta cell raises it by 2. Thus $\nu$ strictly
increases between different marks, also up to $\top$. Hence two members
of one fibre have different seeds. Their acquired complete anchors
$\mathsf A(j(u))$ differ, because those tables recover $j(u)$ and $u$.
Theorem 11.5 proves that these are the actual held tables at these cuts.
This separation uses their acquired contents, not an inferred snapshot
or a freely supplied old-source table.

For the successor assertion, fix one fibre and its common decoded
source $z$. Formula (ER.57) gives at most one member per mark, so
different members have different marks. Every nonterminal candidate
mark $p$ is a leaf of $z$.
That original leaf has not yet been changed, so its current label is
exactly the acquired old label used by the next guard. Definition 11.3
and Theorem 11.5 therefore give the actual next source

$$
 r^+(e(u,p))=
 \begin{cases}
 E\bigl(z[p\leftarrow\rho(z|_p)]\bigr),&p\ne\top,\\
 E(z),&p=\top.
 \end{cases}
\tag{ER.60}
$$

Here $z|_p$ is that leaf and the substitution notation changes just its
occurrence. This equation describes the enabled guarded patch, rather
than a hypothetical diagnostic action. Two different leaf positions of
$z$ are incomparable. At one of them one successor has the changed
logical label or subtree, while the other has its unchanged leaf.
Since $\rho(\alpha)\ne\alpha$ and $\rho(\beta)\ne\beta$, those logical
successors differ. Each also differs from the unchanged $z$ of the end
case. Injectivity of $E$, already supplied by substitution injectivity,
separates their actual source successors. The $\top$ successor is
exactly Read0($\mathsf U,\varepsilon$), with its completion record and
unchanged source. At every other mark the successor is the next Edit
cut with its actual patch record. All other retained fields stay in the
full successors required by Definition 11.4. Thus source projection
already separates these complete responses, without discarding any of
their remaining fields. $\square$

**Theorem 13.3 (an attained unbounded exact fibre).** For $d\ge1$ let
$t_d$ be the perfect ordered binary tree of height $d$ with all leaves
$\beta$, and put $n=2^d$. Order its leaf addresses as
$q_0<\cdots<q_{n-1}$ in left-first order. For $0\le k\le n$, let
$u_{d,k}$ have the same perfect shape, with its first $k$ leaves
$\alpha$ and all remaining leaves $\beta$. Set

$$
\begin{aligned}
p_{d,k}&=Rq_k &&(k<n),& p_{d,n}&=\top,\\
e_{d,k}&=e(u_{d,k},p_{d,k}),&
z_d&=\langle b_2,t_d\rangle,& r_d&=E(z_d).
\end{aligned}
\tag{ER.61}
$$

Then the complete fibre over $r_d$ within $\mathcal E_1$ consists of
exactly these $n+1$ cuts. Its members share the same labelled current
source, source support and terminal boundary, pending U, Edit family,
held role and empty finished-command word. They have pairwise different
actually acquired anchors and next enabled source successors. Their
source height and exact fibre size are

$$
 H_d=h(r_d)=d+3,\qquad
 m(z_d)=2^d+1=2^{H_d-3}+1.
\tag{ER.62}
$$

Even if Edit($\top$) is excluded, the nonterminal Edit subdomain has
exactly $2^d$ members over this same source.

Proof. Every nonempty all-beta labelled tree belongs to $I$: its beta
leaves belong to $I$ and the paired-image production closes $I$ under
pairing. Its inverse is the same ordered shape with all leaves alpha.
For this last assertion, at a branch with all-beta descendants the
exceptional production $\langle\beta,\alpha\rangle$ cannot apply;
$\delta$ therefore preserves the branch and recurses into both children.
Consequently every leaf of $t_d$ passes the sibling-image tests, and
$D_{q_k}(t_d)$ changes precisely the earlier leaves to alpha. It is
exactly $u_{d,k}$. Also $\delta(t_d)=u_{d,n}$. Formula (ER.57) proves
that these are all candidates, not merely a selected colliding list.

In the actual run for $u_{d,k}$, first the two alpha leaves of $a_0$
are patched, then exactly the first $k$ alpha leaves of the seed are
patched. All become beta; every remaining seed leaf was already beta
and has not yet been patched. Thus the current logical tree is exactly
$z_d$, with the claimed frontier and actual old anchor. This gives a
direct realization under the unchanged startup as well as the image
argument. For $k<n$ the next actual patch replaces the B tile at $Rq_k$
by $\langle B,A\rangle$; for $k=n$ the next step leaves the source
unchanged. Their separation is Theorem 13.2.

The height of $E(b_2)=\langle B,B\rangle$ is 3. The height of
$E(t_d)$ is $d+2$, because every leaf tile B has height 2. Hence
$h(r_d)=1+\max(3,d+2)=d+3$ for $d\ge1$. Counting the $n$ leaves
and the one end candidate gives (ER.62). Removing the end cut removes
exactly that candidate. $\square$

## 14. Necessary supplementary information and stationary source acquisition

**Definition 14.1 (conditional supplement and source-only comparison).**
A supplementary name is a function $C$ on $\mathcal E_1$ with a fixed
comparison alphabet, intended to accompany the current source description
or an acquisition of that source. For a decoded source $z$, its
conditional capacity is the cardinality

$$
 \kappa_C(z)=|\{C(e):(u,p)\in\mathfrak F(z),\ e=e(u,p)\}|.
\tag{ER.63}
$$

This is an extensional information function. No effective presentation
of its alphabet, algorithm evaluating $C$ on candidate cuts, equality
test for its values or procedure acquiring the actual value $C(e)$ is
assumed. Supplying a value and computing the assignment are different
requirements.

The name is complete only when it includes every accessible
source-dependent or history-dependent distinction beyond public fixed
inputs and the current source itself. In particular this includes any
available actual anchor or old table, leaf list, selected row or frontier,
control operand and latch, previous reply or emitted frame, patch count,
primitive ordinal, original acquisition transcript, event or retired-tile
archive, scratch contents, list lengths and address backing. It also
includes exposed allocation numbers, object identities, handles,
allocator state, variable permission/binding information, scripts,
source-dependent scheduling, timing and output length. Information may
be shared, but every accessible joint distinction is counted in $C$.
Fixed owner, source occurrence, root, program and rights are public
comparison fields; they carry no seed-dependent choice. A transcript
of additional source-only queries is considered below. This is the
complete-name convention of Assumption 1.3 applied to this source fibre.

Define $\mathcal O_{\rm src}$ as a separate stationary comparison
interface: on the source present at an Edit cut, a source-blind
observer with common initial local data may issue finite original-root
literal queries, adaptively using only public inputs, any explicitly
supplied supplement $C$, and the replies already obtained. The source stays fixed throughout such an experiment.
The sole source-dependent return of a query is its truthful four-valued
literal. Its other local computation, choice of address and stopping
rule are deterministic functions of these data. Any additional
accessible distinction just listed must instead enter $C$ explicitly;
there is no side-channel reply supplied for free.

This is an interface for comparing information on stationary source
versions. In $Q_\partial$ itself no literal-query interrupt is enabled
at Edit: its only enabled action there is Advance, which performs
(ER.60). In particular $\mathcal O_{\rm src}$ neither pauses that
controller as a newly installed service nor changes its transition
table. Query counts, address lengths, decoding and delivery in this
comparison remain charged operations whenever realized.

**Theorem 14.2 (sharp conditional necessity on the actual source fibre).**
Suppose a decoder from current source and complete supplementary name
correctly recovers, on all of $\mathcal E_1$, any one of the following:
the actual held anchor, the actual next source successor under Advance,
or the actual $Q_\partial$ cut. Then on every attained source fibre
$C$ is injective and

$$
 \kappa_C(z)=m(z).
\tag{ER.64}
$$

The same requirement holds if the current source description is
replaced by source support, terminal boundary or any terminating
$\mathcal O_{\rm src}$ acquisition. Conversely, conditional on a fixed
source $z$, the explicit rank encoding below uses exactly $m(z)$
supplementary values and suffices to recover the cut and its full
$Q_\partial$ response map. Thus this conditional cardinality is sharp.
In particular a fixed-width binary supplement valid on the family
(ER.61) requires, and conditionally can attain,

$$
 b_d=\left\lceil\log_2(2^d+1)\right\rceil=d+1=H_d-2.
\tag{ER.65}
$$

On the nonterminal-only family the corresponding exact capacity is
$2^d$ and fixed width is $d=H_d-3$. No single fixed finite supplementary
alphabet suffices over all these attained heights. This is a lower
bound for a subdomain of the full declared domain, and therefore also
for any complete supplementary interface required on all of
$\mathcal H_\partial$ with these same recovery demands.

Proof. By Theorem 13.2 the target values of each of the three specified
tasks are pairwise different on every fibre. If two members have the
same $C$ value, a decoder with that same source and name has equal
inputs and cannot return both distinct targets. This proves
injectivity and (ER.64); the image cannot have more than the number of
members. This counting step is the elementary pigeonhole argument
already used in Theorem 3.1 and AIF §§4–5, reused here. The new premise
is the exhaustive actual-source fibre and its acquired-anchor and
source-successor separation, not a new general counting theorem.

Support and boundary determine the same $z$ by ABT and prefix closure,
so they give exactly the same obstruction. For a stationary query
acquisition, fix equal $z$ and equal $C$. The first submitted address
is equal. Its truthful reply is equal because the labelled sources
are equal. Induction gives equal subsequent addresses, replies,
accessible local states and stopping decisions. Hence no such
transcript separates those two members, regardless of the number or
lengths of its queries. Any additional source-dependent timing,
allocation or prior record escaping this induction is, by Definition
14.1, part of $C$ and must be counted. The argument uses equality of
actual literal functions, rather than a bound on queries or a failure
to inspect sufficiently deep positions.

For sufficiency on a fixed fibre, enumerate (ER.57) in left-first mark
order, with $\top$ last, and assign ranks $0,\ldots,m(z)-1$. The rank
selects exactly one recovered pair $(u,p)$. The already proved partial
inverse and Theorem 11.5 then reconstruct that cut and full joint state;
Definition 11.3 supplies its entire lawful partial response map,
including complete original successors, retired material and records.
This is an information encoding on the attained fibre. It does not
claim that a source-only observer can obtain the rank. The actual
controller already has the distinguishing frontier in its receipt,
backed by the acquired leaf list; translating its description to a
rank is finite additional local computation if requested.

For (ER.61), the ranks are exactly $k=0,\ldots,2^d$. A binary word of
length $d+1$ can encode them, whereas $d$ bits have only $2^d$ values.
This proves (ER.65) without a probability distribution or an average
coding assumption. Excluding $\top$ leaves precisely $2^d$ ranks.
Unbounded $d$ excludes a uniform finite alphabet. A correct interface
on the full domain restricts to a correct one here, proving the final
lower-bound assertion without changing that full domain. $\square$

**Theorem 14.3 (what stationary source acquisition determines).** On
$\mathcal E_1$, complete stationary literal acquisition under
$\mathcal O_{\rm src}$ determines exactly the finite candidate list
(ER.57), its candidate held anchors and its candidate next source
successors. It recovers the actual one of these without supplementation
if and only if $m(z)=1$. When $m(z)>1$, even full labelled-source
disclosure and arbitrarily many stationary queries do not select it.
With a complete supplementary name, exact recovery on a fibre is
possible set-theoretically if and only if that name separates its
members. Effective recovery is supplied here for the explicit
frontier-word and rank encodings, conditional on the actual encoded
value being supplied together with the current source description.

Proof. A finite stationary tree can be acquired by the source-blind
producer of Construction 9.10, using one truthful literal at every
node. Apply the ABT decoder to its acquired description of $r=E(z)$,
and compute (ER.57), (ER.55) and (ER.60). This gives the entire finite
candidate list. On a singleton it supplies the unique actual cut.
On a larger fibre Theorem 13.2 separates the anchors and successors,
while the transcript induction in Theorem 14.2 makes every
source-only experiment identical on its members. Thus it cannot
select among them. If $C$ separates the fibre, each attained pair
$(z,c)$ has a unique member $e$ with $C(e)=c$. Assigning that member
defines the set-theoretic inverse on the attained image. Conversely,
failure to separate gives the equal-input contradiction. This inverse
does not assume evaluation of $C$ or an equality test on its alphabet.
Even when names are represented by natural numbers with decidable
equality, that comparison alone supplies no evaluation of $C$ on the
reconstructed candidates. No effective inverse for an arbitrary
separating $C$ is asserted.

For the explicit frontier encoding, compare the supplied finite
$L/R$ word or $\top$ with the marks in (ER.57). There is exactly one
matching candidate on its actual image. For the rank encoding, select
the entry at the supplied rank in that list's fixed left-first order,
with $\top$ last. Both rules are uniform finite algorithms on the
supplied descriptions: they use the computed candidate marks or list
indices, not evaluations of an unspecified naming function. Theorem
11.5 then reconstructs the cut and complete $J$, and Definition 11.3
gives its full response map. Enumeration, word comparison or indexing,
reconstruction and delivery are additional computations whenever
realized, with their work, workspace and word/reference backing
charged. No uniform runtime or storage bound is supplied here, and
these computations are not part of the prefix subtotals in Proposition
15.1. Neither algorithm acquires its supplementary input from the
source alone.

The producer here is used under the separately declared stationary
comparison interface, not as an additional busy operation of
$Q_\partial$. It can acquire the current source, not its lost original
labels or update frontier. Conversely the existing controller's
actual held anchor or its actual event transcript, when accessible,
is source-dependent supplementary information and is counted as
such. Their availability refutes no source-only assertion, since
neither is a function of $r_d$ across (ER.61). $\square$

## 15. Same-prefix resources, attribution and retained interfaces

**Proposition 15.1 (operation and material coordinates of the exact family).**
For each $e_{d,k}$ of (ER.61), let $n=2^d$. Count from the installed raw
seed through its actual startup and then up to this first-U Edit cut.
All these runs have the exact same literal Read count and total number
of letters submitted by those Read opcodes:

$$
 N_{\rm Read}=6n+5,\qquad
 L_{\rm addr}=(6d+6)n+26.
\tag{ER.66}
$$

Between the first Ready and $e_{d,k}$ there are exactly $k+4$
continuing primitives: one supplied bit, one Select and $k+2$ alpha
cell patches. There are no additional literal Reads, refresh rows,
row-transfer primitives or output tokens in this interval. Its source
patches allocate $5(k+2)$ new tile nodes, retire $3(k+2)$ old tile nodes,
and inspect exactly $3(k+2)$ old tile nodes for their guards. Their
submitted tile-address lengths sum to

$$
 L_{\rm patch}=4+k(d+1).
\tag{ER.67}
$$

At first Ready the active source node count is $6n-2k+7$; at the Edit
cut it is the common value $6n+11$. Each initial logical-anchor
acquisition constructs $8n+12$ query-suffix word links and $2n+2$
logical child-address links. Its initial output frame has $2n+7$
tokens. These are selected same-run subtotals; they do not assert
equality of acquisition histories, source provenance, total work,
retained material or physical storage.

Proof. The perfect seed shape has $N(u_{d,k})=2n-1$ nodes and

$$
 W(u_{d,k})=\sum_{q\in\operatorname{Pos}(u_{d,k})}|q|
   =\sum_{i=0}^d i2^i=2(d-1)n+2.
$$

The last finite-sum identity follows by induction on $d$: adding the
new level contributes $(d+1)2^{d+1}$. The entry
$x_{d,k}=j(u_{d,k})$ has $N(x_{d,k})=2n+3$ nodes. Attaching its
three-node $a_0$ and the seed below one root gives

$$
 W(x_{d,k})=W(u_{d,k})+N(u_{d,k})+W(a_0)+N(a_0)
           =2dn+6.
$$

The actual initial raw traversal uses $N(u_{d,k})$ Reads; startup
logical acquisition uses $2N(x_{d,k})$. All later steps before this
cut are input, Select and guarded patches, whose source probes are
separate from literal Read opcodes. Substitution in (ER.53), with
no finished transactions, therefore gives

$$
\begin{aligned}
 N_{\rm Read}&=(2n-1)+2(2n+3),\\
 L_{\rm addr}&=W(u_{d,k})+2W(x_{d,k})+4N(x_{d,k}),
\end{aligned}
$$

which are (ER.66). The address words and node counts agree across the
family because both the raw seeds and their logical entries have the
same ordered shapes. Their actual replies do not agree: already the
initial seed traversal distinguishes the alpha-prefix labels. The
logical anchor replies and the emitted startup frames also distinguish
those labels. Equal query counts and submitted-word lengths therefore
do not erase their different actual acquisition histories.

The two leaves $LL,LR$ of $a_0$ and the first $k$ seed leaves were all
alpha, so all $k+2$ patches are exactly the alpha case of Assumption
11.1: three checked/retired old nodes and five new nodes each. The two
left addresses have length 2, and the $k$ right leaf addresses have
length $d+1$, proving (ER.67). Each step appends its actual event,
so the continuing event-record suffix has $k+4$ entries; their
operands and backing remain charged. For $k<n$, the *next* step is a
beta patch at length $d+1$, allocating nine new nodes, retiring and
checking five old nodes. For $k=n$, the next step is the completion
record with no source patch. These are the actual next steps used
in Theorem 13.3, not a postponed whole-U operation.

There are $n+1$ logical branch nodes in $x_{d,k}$, $k+2$ alpha leaves
and $n-k$ beta leaves. Its encoded node count is consequently
$(n+1)+3(k+2)+5(n-k)=6n-2k+7$. Each completed alpha patch adds two
active nodes, giving $6n+11$ at every displayed cut. Startup logical
acquisition uses the two queries of (ER.46) per logical node, each
with two new suffix links, giving $4N(x_{d,k})=8n+12$ links; its
branch scheduling creates $N(x_{d,k})-1=2n+2$ child-address links.
The output rule gives $N(x_{d,k})+4=2n+7$ tokens. These are startup
acquisition and output counts, not an assumed startup Copy phase.

The startup source preparation, two warm-up substitutions, acquired
rows, tables, source occurrence backing, raw traversal stack, lookup,
all prior/retired material, address traversal, reference identity,
serialization and records keep their existing charges in §§11–12.
In particular long patch addresses are not constant-time seeks; even
equal submitted Read words do not assert equal source-node traversal
work when absence is encountered at different depths. The varying
patch and retirement totals alone preclude inferring equal total cost
from (ER.66). No total-storage optimum follows from the common active
node count. $\square$

**Definition 15.2 (information coordinate and supplier boundary).**
The lower coordinate in (ER.64) is the number of distinct complete
supplementary values *conditional on a current source*. Equation
(ER.65) is its zero-error fixed-width binary encoding cost. A variable
length, pointer identity or backing geometry that distinguishes members
belongs to the name under Definition 14.1. It cannot evade the bound
by being omitted from a displayed payload. The bound requires no new
physical cells when existing acquired material already supplies the
necessary distinctions; the actual anchor and receipt do so here.

On (ER.61) a nonterminal receipt address $Rq_k$ has length $d+1$,
and the end case has its fixed token. The source description determines
$d$. Thus the conditional rank code attains $d+1$ bits, while the
existing actual receipt supplies at most $d+1$ address letters plus
fixed tags. For the whole domain the supplied word-description bound
remains $h(r)+c$ from Proposition 12.3. To compare binary information
on the same coordinate, fix a current source of height $H$. Its receipt
has at most one word of length at most $H$, or the end token. Including
all word lengths and that token gives

$$
 1+\sum_{i=0}^{H}2^i=2^{H+1}
$$

possible address-field values. A phase without an address can use the
empty word in this encoding, since the phase tag specifies its absence.
Let $K$ be a fixed bound on the number of finite phase/command/reply-tag
tuples. Thus at most $K2^{H+1}$ complete extensional receipt values
occur, with a fixed-width encoding of at most
$H+1+\lceil\log_2K\rceil$ bits. This count includes word length and the
end token; it does not suppress them as side channels. Theorem 11.5
makes every remaining field of $J$ a function of this source and receipt.
More precisely, let $B(H)$ be the least fixed binary width sufficient
for a complete supplementary name uniformly on all cuts of
$\mathcal H_\partial$ whose current source has height $H$, conditional
on that source and this fixed model. This is a conditional
description-width quantity. Its upper bound uses the explicit receipt
encoding and the effective reconstruction of Theorem 11.5 on supplied
source and receipt descriptions; it invokes no effective inverse for
an arbitrary supplementary function. Acquiring, encoding, reading and
using that receipt retain their separate work and material costs.
Taking $d=H-3$ in (ER.61) gives its lower bound, so

$$
 H-2\le B(H)\le H+1+\lceil\log_2K\rceil\qquad(H\ge4).
$$

This is a worst-case comparison at each attained height. A particular
singleton source fibre needs no supplement on $\mathcal E_1$; the
family (ER.61) has the explicit exact conditional width $H_d-2$.
The bounds compare the same variable, supplementary information, and
do not identify it with physical address backing, whole-memory size,
all retained source history, runtime or a universal bit lower bound.

The source-specific content of §§13–15 is repo-derived: the exhaustive
first-U fibre (ER.57), its actual anchor and next enabled source
separation, the fully realized perfect-tree family and exact exhaustion,
and their necessary-information and same-prefix consequences. Repository
suppliers here designate the fixed text at
$\texttt{09d4a7e32b723bd50b1cfc839724a624544a0320}$.
Theorem 10.2 supplies the marked inverse and its image tests; Theorem
11.5 supplies acquisition, leaf-list actuation and canonical actual
prefixes; Theorem 12.2 supplies the four independent full-domain kernels
and full successors; Proposition 12.3 supplies the counted primitive
rules. None of their inverse or replay conclusions is reproved as new
content. ABT Theorem 12.1 supplies erased-source decoding. The
[Intrinsic Substitution Coordinates declarations][ERISC], including
`pair_image`, `no_alpha` and private `substitution_injective`, and their
[owning Scribe][ERISCB], supply the image grammar and injectivity.
[Native Full Source Producer][ERPROD], its private `traverse`,
`production_reads`, `stationary` and [owning Scribe][ERPRODB], supply
the actual stationary initial traversal under unbounded finite workspace.
Reading those statements is not an additional Lean verification.

The generic equal-input and finite-alphabet counting arguments are
reuse from Theorem 3.1 and [AIF §§4–5][ERAIF]. The literature-attested
focus/context representation of Huet, *The Zipper*, §§1.1–1.3
([author manuscript](https://pauillac.inria.fr/~huet/PUBLIC/zip.pdf)),
retains a focus together with surrounding siblings and a path; it does
not enumerate the different old seeds consistent with this one present
partially substituted source. The literature-attested history tape and
history/copy/reverse construction in [Bennett, Introduction and
three-tape construction][Bennett] likewise supplies a comparison for
retaining distinctions and charging records, not this exact source
fibre or its old-anchor acquisition. Neither literature comparison
is used as a physical-storage bound, nor is the source-specific
deduction a claim of worldwide originality.

**Definition 15.3 (preserved kernels and open operational interfaces).**
The four views remain exactly (ER.49), with their individual diagonal
$Q_\partial$ kernels and all full response/successor transports in
Theorem 12.2. In particular $S_\partial$ and $B_\partial$ still include
the actual receipt. Forgetting its frontier on $\mathcal E_1$ produces
the coarser source fibres studied here; it does not replace either view
or assert a new all-cut kernel theorem. $T_\partial$ retains the actual
acquisition and event history, and $M_\partial$ retains the acquired
anchor, role and receipt. Their different records and physical backing
are preserved in $J$ and its complete successors. The same-run
counts above do not identify those histories or erase their provenance.

The stationary comparison interface of Definition 14.1 installs no
busy interrupt, diagnostic, controller or acquisition service. Effective
recovery from the explicit frontier, rank or receipt encoding assumes
its actual supplied value; the arbitrary-name sufficiency of Theorem
14.3 is only set-theoretic. No evaluator or means of obtaining an
arbitrary $C(e)$ is installed. Manipulation of a recovered description
does not grant access to a historical cut, new observer rights,
authenticated handoff, returned
conversion, interruption authority or a physical lowering. Those
remain separate operational interfaces in Definition 12.6. The
pre-first-Ready four-kernel extension, finer cuts inside the declared
atomic primitives, other owners and independently interleaved requests
also remain outside this theorem.

The first-U restriction is used only to prove a necessary-information
bound inside the unchanged full declared domain. Initialization and
actual acquisition have not been replaced by an all-beta source
supplied as advice: the different $u_{d,k}$ are the actual initially
installed seeds, and $r_d$ is their attained common partial-update
source. This addition supports the source-specific parsimony question
of how many frontier distinctions must accompany current geometry.
It supplies no solution of the original prediction task (ER.3), no
extension of original fixed-$G_{gc}$ or original-$Q$ results beyond
their stated hypotheses, no universal alpha/beta reduction, no identity
with physical spacetime and no completion of the sustained four-expression
objective. All original open interfaces listed in Definitions 12.6 and
Open problem 8.1 remain in their stated scopes.

## 追加锚（本行以下为增补区）

## 16. Directed acquired-leaf transitions and their actual operands

**Definition 16.1 (directed refinement domain and literal tiles).** Retain
$\mathcal T,\rho,E=\rho^2,j,F_w,P_p,D_p$ and the acquisition and command
interfaces of §§9–12. The model in §§16–19 is denoted by $\mu$.
Its seeds are all finite $u\in\mathcal T$. Its continuing domain starts
at the actual first Ready, admits every finite lawful supplied bit prefix
of (ER.47), and includes every intervening transition cut. Only the
nonterminal Edit row of Definition 11.3 is replaced. Every other row,
including its source Read, suffix construction, preparation, graft,
refresh, Copy, Bind, lookup and output coeffects, retains its stated
atomic boundary. The additional transitions are those of Definition 16.5.

Write $x=F_w(j(u))$ at the start of a continuing transaction, where $w$
counts finished transactions. In a U transaction $p$ ranges over the
entire *original* leaf list of the actually acquired $\mathsf A(x)$;
$\ell=x|_p$ is its acquired old label. No newly born leaf joins that list.
For a nonterminal original leaf let $p^+$ be its next original leaf, or
$\top$. Put

$$
 C_\alpha=A,\qquad C_\beta=B,\qquad
 D_\alpha=B,\qquad D_\beta=\langle B,A\rangle.
\tag{ER.68}
$$

Thus $C_\ell=E(\ell)$ and $D_\ell=E(\rho\ell)$. The following finite
lists give *all* positions and tags of these tiles, in preorder; a listed
branch has both listed children, and a listed leaf has neither child.

| Tile | Positions in order | Tags in the same order |
| --- | --- | --- |
| $C_\alpha$ | $\varepsilon,L,R$ | $\mathsf{branch},\beta,\alpha$ |
| $C_\beta=D_\alpha$ | $\varepsilon,L,LL,LR,R$ | $\mathsf{branch},\mathsf{branch},\beta,\alpha,\beta$ |
| $D_\beta$ | $\varepsilon,L,LL,LLL,LLR,LR,R,RL,RR$ | $\mathsf{branch},\mathsf{branch},\mathsf{branch},\beta,\alpha,\beta,\mathsf{branch},\beta,\alpha$ |

Write $n_\ell=|\operatorname{Pos}(C_\ell)|$, $m_\ell=|\operatorname{Pos}(D_\ell)|$
and $g_\ell=\sum_{v\in\operatorname{Pos}(C_\ell)}|v|$. Their respective
alpha/beta values are $3/5$, $5/9$ and $2/6$. Each $x$ is compound:
$j(u)$ is compound and each of U, L and R preserves that property.
Consequently every selected $p$ is nonempty. Publication below uses an
actual parent child field; no root-leaf publication rule is presupposed.

**Assumption 16.2 (one owned directed carrier and the operation basis).**
Fix the source, root reference, orientation and sole owner as in
Assumption 11.1 before selecting the finite seed or any future input.
An occurrence has fields $(\mathsf{tag},L,R)$ and no stored parent field.
A child field is either null or an actual occurrence reference. The
active source is the component reachable from the distinguished root.
Detached components and all earlier material remain allocated.
Installation of the seed is a canonical occurrence tree; allocation
uses the next unused name in one fixed typed allocation order. Names
are not additional selected receipt values.

The same owner has static authority over this source, its acquired rows,
local reference cells, word cells, fresh staging and retired material.
It has the following mathematical operations on actually held references:
read one indicated field; follow a nonnull child field; assign one
indicated owned child field; and allocate one fresh occurrence with a
literal tag and two null children, returning its reference. It may read
one indicated acquired row/list/word field, allocate one bounded local
cell from held values, copy or clear indicated bank values, and take a
finite control edge. Each row of Definition 16.5 is one such operation
with its explicitly indicated bounded local coeffects and the event
coeffect of Definition 16.4. No row constructs an unbounded word, scans a
table, decodes an unknown subtree or returns a successful whole-tile test.

The owner capability is an additional premise of $\mu$, distinct from
permission for the old atomic patch. Dispatch first consults the actual
finite control. In particular postpublication maintenance does not test
the former whole-tile admission condition again. There is no competing
writer, independent request, interruption, revocation, name choice or
independent scheduling choice during Busy. No input or output occurs
inside the new fragment. Source traversal during refresh is stationary.
All authority fields and allocation rules are fixed comparison fields
or their deterministic consequences, not advice about $u$ or a history.

The primitive boundary includes one-node initialization and the bounded
local/event coeffects. It does not expose their internal assignments.
A source-node allocation together with an event allocation therefore has
more than one total cell birth. This is a directed mathematical operation
basis, with no asserted reciprocal-parent, native-tape or physical
realization and no fixed-width or unit-time reference convention.

**Definition 16.3 (address backing, bank and initialization).** Choose the
following one backing convention for the backed words of §11. A nonempty
address cell has fields $(\mathsf{prev},\mathsf{last})$ and denotes
$\operatorname{word}(\mathsf{prev})\mathsf{last}$. The empty address has
a fixed distinguished reference. Thus inherited address extension creates
one snoc cell, and inherited row transfer shares its actual reference.
A forward word cell instead has fields $(\mathsf{letter},\mathsf{next})$,
with a different distinguished empty reference. These are material
representations of words, not numerical root-to-position access ports.

A leaf-list cell $c$ has fields $\mathsf{row}$ and $\mathsf{next}$; its
row has the actually acquired address and label fields. This makes explicit
the original leaf-row references of Definition 11.2. Appending a leaf-list
link, including the fixed tail-link assignment, remains its inherited
bounded local coeffect. A list is not copied to supply its next link.
The last cell's next field is $\top$, and the current administrative
cursor is an actual $c$, or $\top$.

There are twenty reference bank slots

$$
 r,p,I,q,v,t,\mathit{cur},\mathit{par},\mathit{old},g,\mathit{nxt},
 N_0,\ldots,N_8
$$

and three finite latch slots $\ell,b,\mathit{side}$. Each slot has a
null value as well as its indicated typed values. The cleanup order is

$$
r,p,q,v,t,\mathit{cur},\mathit{par},\mathit{old},g,\mathit{nxt},
N_0,\ldots,N_8,\ell,b,\mathit{side},
$$

with $I$ omitted. Here $I$ holds an
invocation cell with seven fields

$$
(c,r,p,\ell,\mathsf{old},\mathsf{new},\mathsf{next}).
\tag{ER.69}
$$

The first four fields are fixed on creation. The last three start null
and are filled once, respectively at Locate, the first Birth, and Next.
They retain the actual returned handles through cleanup. The invocation
is selected as active exactly while the bank slot $I$ is nonnull.
The retirement head and completion head are additional owner-local
reference roots, initially empty; both have append-only retained chains.

After the actual initialization to $E(j(u))$ and before the initial
logical acquisition, add a fixed finite sequence: create one holder with
23 null slot fields and two empty head fields, then create its 23
one-value slot cells in the displayed order, installing each returned
reference in its designated holder field. The holder is attached to the
owner's fixed local root. These 24 bounded transitions, their 24 events,
all holder/slot field initializations and root attachments are charged.
The two head references reside in that holder; the inherited finite
control carries the added finite tags. All bank slots are initially
null. The holder and slot layout is independent of $u$ and future input.
The raw initial traversal, known startup preparation, actual source
initialization and logical acquisition are still performed. The first
Ready is reached only after that acquisition and the inherited startup
lookup/output. No source-dependent table or handle is inserted as advice.

**Definition 16.4 (actual records and bounded coeffects).** Every executed
row appends exactly one fine event to the actual chronological chain.
An event contains its predecessor reference, row opcode, actual operand
references, acquired reply or literal emitted token when any, and the
bounded local assignments of that row. Each tuple has a fixed finite
arity for that opcode; null padding gives one common finite bound since
there are finitely many row shapes. Tuple fields are part of this
abstract cell's payload, not free auxiliary cells. Every event field
initialization, read of the old tail and assignment of the new tail is
included in the resource account. An event contains no unrestricted
snapshot or arbitrarily chosen historical payload. Only actual execution
at the actual tail creates it. The initial truthful acquisition record
and all inherited continuing events are retained as well.

A retirement cell contains $(\mathsf{oldroot},\mathsf{previous},I)$.
CellDone additionally creates one completion cell containing the coarse
Edit opcode and the seven actual values in (ER.69), together with its
previous-completion reference. These values are read from $I$ in that
bounded row, before clearing the bank's invocation reference. This
completion cell and CellDone's fine event are distinct births. Earlier
rows have fine events but no completed Edit cell. Retained references
and events keep cleared referents allocated; clearing never deletes a
word, node, row, invocation or record.

A successful field-test row acquires the indicated actual field value,
checks only its stated null/tag/reference predicate, records that value,
and takes the indicated edge. A false predicate has no executing edge,
no fine event and no successor. An action not enabled at the present
control likewise returns $\mathsf{none}$ without execution. These are
partial transition rules, not an assumption that the tests succeed.
Theorem 17.1 proves their success on the entire admitted domain.

**Definition 16.5 (complete replacement of the nonterminal Edit row).**
All row labels below are distinct finite control positions. Indices over
tile positions, their path letters, fields and bank slots range over the
fixed lists of Definitions 16.1 and 16.3. They are finite tags, not
unbounded counters. At Edit($p$), $p\ne\top$, call the entry position
$E_0$ and retain the actual administrative leaf cursor $c$.
The following table gives every edge of the fragment. A stated register
assignment is a bounded coeffect of that row; unmentioned fields persist.
Every edge also has exactly Definition 16.4's fine event coeffect.

| Position | Operation, bounded local effect and next position |
| --- | --- |
| $E_0$ | Read $c.\mathsf{row}$ into $r$; go to $E_1$. |
| $E_1$ | Read $r.\mathsf{address}$ into $p$; go to $E_2$. |
| $E_2$ | Read $r.\mathsf{label}$ into $\ell$; go to $E_3$. |
| $E_3$ | Create $I=(c,r,p,\ell,\varnothing,\varnothing,\varnothing)$, set $q=p$ and $v$ to the empty forward word; go to RevTest. |
| RevTest | Test the held $q$ against the empty snoc reference. If empty go to SeekInit; otherwise go to RevLast. |
| RevLast | Read $q.\mathsf{last}$ into $b$; go to RevPrev. |
| RevPrev | Read $q.\mathsf{prev}$ into $t$; go to RevPush. |
| RevPush | Create the forward cell $(b,v)$ and put its returned reference in $v$; set $q=t$, clear $t,b$, and go to RevTest. |
| SeekInit | Set $\mathit{cur}$ to the actual retained source-root reference and $q=v$; go to SeekTest. |
| SeekTest | Test $q$ against the empty forward reference. If empty go to Locate; otherwise go to SeekLetter. |
| SeekLetter | Read $q.\mathsf{letter}$ into $b$; go to SeekNext. |
| SeekNext | Read $q.\mathsf{next}$ into $t$; go to SeekFollow. |
| SeekFollow | Follow $\mathit{cur}.b$, requiring nonnull. Save the old $\mathit{cur}$ in $\mathit{par}$ and $b$ in $\mathit{side}$; put the returned child in $\mathit{cur}$, set $q=t$, clear $t,b$, and go to SeekTest. |
| Locate | Copy $\mathit{cur}$ into $\mathit{old}$ and $I.\mathsf{old}$; go to the first GuardReset. |
| GuardReset$(i)$ | Set $g=\mathit{old}$; go to the first GuardFollow for the old tile's $i$th position, or its GuardTag if that position is empty. |
| GuardFollow$(i,j)$ | Follow the $j$th literal letter of that fixed position from $g$, requiring nonnull, and replace $g$ by the child; go to its next letter, or GuardTag$(i)$. |
| GuardTag$(i)$ | Probe $g.\mathsf{tag}$, requiring the $i$th literal old tag; go to GuardL$(i)$. |
| GuardL$(i)$ | Probe $g.L$, requiring nonnull at a listed branch and null at a listed leaf; go to GuardR$(i)$. |
| GuardR$(i)$ | Probe $g.R$ with the same branch/leaf requirement; go to the next GuardReset, or the first Birth after the last old position. |
| Birth$(i)$ | Allocate the $i$th target node with its literal tag and null children into $N_i$. For $i=0$ also set $I.\mathsf{new}=N_0$. Go to the next Birth, or the first LinkCheck after the last birth. |
| LinkCheck$(i)$, $i>0$ | Probe the designated child field of the bank-held parent of target position $i$, requiring null; go to LinkWrite$(i)$. |
| LinkWrite$(i)$, $i>0$ | Assign that one staging child field the held $N_i$. Go to LinkCheck for the next nonroot target position, or AttachCheck after the last. |
| AttachCheck | Probe $\mathit{par}.\mathit{side}$, requiring equality to $\mathit{old}$; go to Publish. |
| Publish | Assign that one source child field $N_0$; go to Retire. |
| Retire | Create $(\mathit{old},\mathsf{retirementhead},I)$, install its returned reference as retirement head, and go to Next. |
| Next | Read $I.c.\mathsf{next}$ into $\mathit{nxt}$ and $I.\mathsf{next}$; go to Handoff. |
| Handoff | Set the administrative leaf cursor to $\mathit{nxt}$; go to the first Clean. |
| Clean$(j)$ | Clear the $j$th bank slot in the fixed order of all 22 slots other than $I$; go to the next Clean or CellDone after the last. |
| CellDone | Read the seven invocation fields, create and link the completion cell of Definition 16.4, clear bank slot $I$, and enter inherited Edit at that invocation's $\mathsf{next}$. |

The target parent in a link is the literal immediate-prefix position in
Definition 16.1; its bank index is fixed by the finite list. Every
nonroot target position occurs exactly once in the link list. The
nonempty target lists make the indicated first/last edges unambiguous.
Next uses the retained invocation's original $c$, even after Handoff
changes the administrative cursor. Reading that retained reference and
its one next field, like reading a designated bank slot, is a bounded
reference coeffect. The seven-field inspection in CellDone is explicitly
part of its atomic local row, with seven charged field reads.

Before $E_3$, the initiating cursor is still the original $c$. Afterwards
it is retained in $I$. In particular cleanup never clears $I$ or its
contents. Its old/new/next references are obtained only by the displayed
walk, birth and list read. No event archive is consulted by any row.
After CellDone the next nonterminal Edit starts at $E_0$ with null bank
slots; Edit($\top$) has exactly the inherited completion/refresh row.
There is no extra looping or idle row. All other controls, inputs and
outputs are precisely those of Definition 11.3 with this replacement.

**Definition 16.6 (receipt, complete state and independent fine task).**
Outside the replacement fragment let $f_\mu$ be Definition 11.4's
receipt. Inside it let $f_\mu$ contain the actual finite position of
Definition 16.5, the initiating backed word $p$, the acquired $\ell$
when latched, and the actual word value of $q$ only in RevTest through
RevPush or SeekTest through SeekFollow. Include the finite $b$ latch
only between its letter read and use. At the entry positions $p$ is the
word bound to the still-original cursor; after $E_3$ it is the word bound
to $I.p$. The label is absent until $E_2$ executes, then is retained
through $I.\ell$, including after its separate bank latch is cleared.
The finite position distinguishes snoc-prefix from forward-suffix $q$.
No other bank reference identity, allocation number, seed, finished word,
transaction count, event ordinal or archive key is observed. Word values
and anchor equality use the extensional binding convention of Definition
11.4. Their material acquisition or serialization remains charged.

Let $\mathcal H_\mu$ be all pairs consisting of a finite installed seed
and a finite lawful executed prefix from its actual first Ready in this
relation. The empty prefix, unfinished leading input 1, every entry and
exit of the displayed rows, partial address preparation, every guard and
link, postpublication maintenance, partial refresh, Copy, Bind, lookup,
output and Finish all belong. There is no requirement to supply future
bits or Advances before stopping a finite prefix.

Let $J_\mu$ be the complete actual joint state: active source and root,
all allocated detached and retired occurrences, source/table/address/
reference bindings, acquired anchors and their roles, partial work and
replacement lists, holder/bank/invocation/retirement/completion material,
allocation state, finite control and latches, input record, chronological
records, output buffers/frames and all ownership and rights fields.
The common canonical initialization and every listed coeffect are included.

Define $Q_\mu$ independently of any geometric view. Its present readout
is the actual authorized acquired anchor, its live/held role and
$f_\mu$. Its actions are Supply(0), Supply(1) and Advance. Supply is
legal exactly at inherited Ready and Tail; there both bits are legal.
At other attained controls only the prescribed Advance is legal.
A disabled trial has value $\mathsf{none}$ and causes no executing
successor, record append or output. A successful response is

$$
\bigl(a,\mathsf{legal},\mathsf{ok},\mathsf{opcode},
 \mathsf{actual\ reply/token},\Delta\Gamma_\mu,
 \Delta\mathsf{Out},J'_\mu\bigr).
\tag{ER.70}
$$

The completion-cell append, when present, belongs to $J'_\mu$ and is
referenced in the actual event. The successor in (ER.70) includes every
component just listed; it is a mathematical response coordinate, not
an extra transmitted snapshot. Finite response maps compose these partial
rules and include the empty experiment's present readout. Equality of
$Q_\mu$ profiles means equality of present readouts, lawful domains,
all such complete responses and disabled behavior. This task declares
responses at the new controls; it is not an extension theorem for the
unchanged original prediction task (ER.3).

## 17. Source framing and recovery at every attained fine cut

**Theorem 17.1 (actual enablement, finite completion and source relation).**
Under Assumption 16.2 and Definitions 16.1–16.5, for every finite seed,
every lawful finite continuing input prefix, every U transaction and
every selected original old leaf $p$, all displayed operands are actually
acquired, all attained field tests succeed, and the fragment completes
in finitely many prescribed Advances. Its only active-source assignment
is Publish. If $x=F_w(j(u))$ is the held logical predecessor, then at
every fragment cut the actual source $r$ satisfies

$$
\begin{aligned}
 r&=E(P_p(x)) &&\text{before Publish executes},\\
 r&=E\bigl(P_p(x)[p:=\rho\ell]\bigr)
    =E(P_{p^+}(x)) &&\text{after Publish, through CellDone's entrance}.
\end{aligned}
\tag{ER.71}
$$

The anchor remains the authentic held $\mathsf A(x)$ throughout. The
fragment retires the actual old tile, advances the original leaf cursor
once and creates exactly one completed Edit cell. Its exit has the
inherited Edit($p^+$) source/frontier/anchor postcondition and null bank
slots. Composing these fragments with the inherited rows gives finite
completion of every continuing transaction whenever its prescribed
Advances and input bits are supplied.

Proof. Use the actual acquisition induction of Theorem 11.5, with the
same two-query replies and the backing convention of Definition 16.3.
It supplies the old list, addresses and labels from the same actual
$E(x)$, rather than a proof-side list of unknown leaves. Distinct
original leaves are prefix-incomparable. Induct on that list: completed
earlier fragments replace only their own tiles, so every unprocessed
old tile at $p$ is still $C_\ell$, with every proper-prefix attachment
unchanged. No selected $p$ is empty by Definition 16.1.

The entry reads follow the held list and acquired row and hence obtain
that actual $p,\ell$. After $k$ RevPush occurrences, the snoc cursor
represents the prefix of $p$ of length $|p|-k$, and $v$ spells its removed
suffix in forward order. This holds initially with empty $v$; reading
the last letter and preceding reference, then prepending that letter,
proves the inductive step. All word operands are actual retained cells.
There are exactly $|p|$ pushes. At SeekInit, $v$ therefore spells $p$.
After $k$ SeekFollow occurrences, $\mathit{cur}$ is the actual source
node at the length-$k$ prefix of $p$, and $q$ is the remaining forward
suffix. Every proper prefix is a branch of the unchanged context.
Thus every required child exists. Since $|p|>0$, the final saved
$\mathit{par},\mathit{side}$ is the actual attachment of the reached
old tile, not a guessed numerical address.

Reset and literal relative follows now reach each specified old node.
The tile is $C_\ell$, so its tag and both child-status probes give
exactly the listed replies. This proves the successful guards from the
frame invariant; success is not an extra initial bit. Every fresh target
handle comes from its own Birth, with the stipulated literal tag and
null fields. The target list has one parent for every nonroot position,
parents preceding children, and uses each designated field once. Hence
each LinkCheck finds null, and the separate writes produce exactly
$D_\ell$ without a cycle or sharing. These nodes are disjoint from the
active source and old tile. All work so far changes only local or
fresh detached material, proving the first line of (ER.71).

The saved parent is outside both tiles. Exclusive ownership preserves
its slot between AttachCheck and Publish, and that check therefore
reads the held old root. Publish writes just the fresh completed root
into that one field. Pairing preservation of $E$ and (ER.68) give its
second line. The identity
$P_p(x)[p:=\rho\ell]=P_{p^+}(x)$ follows directly from the definition:
it substitutes exactly one additional original leaf. Retirement, Next,
Handoff and Clean change no active-source field, so the same equation
holds even after the administrative cursor has moved.

Locate retains the old root before overwrite; Retire links it before
any scratch clear. The invocation also retains old and new roots and
the actual next cursor. Thus CellDone reads actual acquired/born operands
after cleanup. Every edge is authorized by the stated static capability,
including postpublication edges whose former tile shape is no longer
at $p$. This proves continuing permission for this declared model,
without deriving a right from its inverse. Exactly one edge creates the
completion cell. Its successor leaves CellDone, clears $I$ and moves
to a different original leaf or $\top$. No second completion for that
invocation is reachable. All other bank slots have already been cleared.

The two word loops decrease finite lengths; every other index follows
a fixed finite acyclic list. The fragment therefore terminates. Induction
over all original leaves, including the last, yields $E(\rho x)$ at
Edit($\top$). No new leaf has been inserted into that old list.
The unchanged refresh, replacement, lookup and output proof of Theorem
11.5 then applies to the actual resulting source. The oriented graft
transactions retain their own unchanged finite proof. This establishes
the assertion uniformly over every finite seed and continuing command
prefix. A finite prefix may stop at any intermediate cut; completion
is conditional only on supplying its prescribed further actions. $\square$

**Definition 17.2 (four independently specified observations).** On
$\mathcal H_\mu$ define

$$
\begin{aligned}
 S_\mu(h)&=(\operatorname{Pos}(r(h)),f_\mu(h)),\\
 B_\mu(h)&=(\operatorname{LeafPos}(r(h)),f_\mu(h)),\\
 M_\mu(h)&=(A_*(h),\operatorname{role}(A_*(h)),f_\mu(h)),\\
 T_\mu(h)&=\Gamma_\mu(h).
\end{aligned}
\tag{ER.72}
$$

Space observes actual ordered child reachability in the active source,
with colours erased. Boundary observes the actual terminal addresses of
that source. Both additionally observe exactly the declared local receipt,
and neither includes staging, retirement geometry, table payload or an
event archive. Memory observes the one genuinely acquired owner-local
anchor, with its actual role and control receipt. Its rows supply the
operands in Definition 16.5 and are used again by the inherited lookup/
output after refresh. It does not include the old-table archive or
chronology as another payload. Time observes the retained order of actual
occurrences, including truthful startup replies and the fixed bank
initialization, without an appended endpoint snapshot. It is not a
physical duration. These definitions select actual material, incidence
and occurrence order before constructing any inverse. Mathematical
observation does not grant another principal access to that material.

**Lemma 17.3 (unique actual local position).** Every attained cut of
$\mu$ has a unique form $(u,w,f_\mu)$, where $w$ is the finished
transaction word. That form determines the entire executed continuing
prefix and complete $J_\mu$. Within a fragment the two observed words
have total length at most $2|p|$; all other receipt components range over
one fixed finite set independent of seed and history.

Proof. Fix $u,w$ and the indicated current pending command or ingress
prefix. The common initialization, completed transactions and all
inherited rows have their deterministic rules. In a U transaction the
held anchor fixes the original finite leaf list. Its addresses are
visited once, so the initiating $p$ identifies one invocation.
Each entry, guard-path/probe, birth, link, publication, retirement,
handoff and cleanup tag occurs at most once in that invocation.
The finite indices are part of the actual position, including each
separate reset and field probe.

For a repeated reversal tag the observed $q$ is a proper shorter prefix
after each push; distinct lengths give distinct word values. RevLast,
RevPrev and RevPush distinguish the separate reads and creation while
that prefix remains fixed. For a repeated seek tag, $q$ is a proper
shorter suffix after each follow. SeekLetter, SeekNext and SeekFollow
distinguish the letter/next acquisition from the source follow. The
empty tests also have their own positions. Hence no fixed
$(p,\mathsf{position},q)$ recurs. A pending finite letter is an actual
latched value, determined by the appropriate read. In the remaining
positions there is no repeated loop at all. The initiating $p$ survives
Handoff through $I$, so these cuts cannot be mistaken for work on the
next cursor. CellDone then changes to the next inherited Edit receipt.

Outside the fragment the unique-position argument of Theorem 11.5
applies: its node/row/output cursors and subphases still occur once.
Inserting the deterministic complete fragments before a later inherited
position introduces no choice. Ready and Tail determine respectively
no pending input and the one acquired leading 1; every other control
fixes its pending command. Thus $(u,w,f_\mu)$ identifies one finite
executed prefix when attained. Executing that determined prefix on the
recovered finite description gives every actual identity, partial word
chain, detached component, table, event, output and rights field under
canonical naming. This use of deterministic execution follows the
position proof; it is not a supplied history index. Finally $q$ is always
a prefix or suffix of $p$ when observed. The stated bound follows from
the finite tag/latch lists. $\square$

**Theorem 17.4 (four separate exact attained-image inverses).** Each
individual observation in (ER.72) has a finite effective inverse on its
actual image to the same $h\in\mathcal H_\mu$ and complete $J_\mu(h)$.
For each $V\in\{S_\mu,B_\mu,M_\mu,T_\mu\}$, its decoder $d_V$ satisfies

$$
 d_V(V(h))=h,\qquad V(d_V(v))=v\quad(v\in\operatorname{im}V).
\tag{ER.73}
$$

These inverses cover entry, address preparation and positioning,
construction, publication, retirement, cursor lag, cleanup and completion,
as well as every inherited live/held phase.

Proof. First consider source support at a fragment cut. Theorem 17.1
proves that the actual active source stays a full $E$ image. Reuse ABT
Theorem 12.1 to decode its erased support to a labelled logical tree $z$.
Before Publish, $z=P_p(x)$, so Theorem 10.2 gives $x=D_p(z)$; this also
recovers $\ell=x|_p$ at entry before its row read has latched it.
After Publish and until CellDone, check $z|_p=\rho\ell$ and put

$$
 z_0=z[p:=\ell],\qquad x=D_p(z_0).
\tag{ER.74}
$$

Theorem 17.1 proves $z_0=P_p(x)$, so (ER.74) is justified on every
such cut, including after Handoff and after scratch clearing. At
CellDone's successor use the inherited next-frontier inverse. Equivalently,
at every fragment cut where the label is latched, the source-specific
normalization is

$$
 \bigl(S\setminus p\{L,R\}^{<\omega}\bigr)
       \cup p\operatorname{Pos}(C_\ell)
   =\operatorname{Pos}(E(P_p(x))).
\tag{ER.75}
$$

The equality follows from the proved exterior frame and the actual old
or new focus in (ER.71). It is a descriptive normalization, not an
operation that restores or copies the unknown source.

Apply Theorems 9.3 and 9.5 to this recovered $x$ to obtain the unique
$u,w$. Lemma 17.3 now supplies the exact fine prefix and full state.
Outside fragments the source cases of Theorem 11.5 are unchanged:
Ready/Tail/Select/Graft decode $x$; inherited Edit($\top$) uses
$D_\top$; Read0 through Finish decode $y=F_{wa}(j(u))$, whose ancestry
word loses the pending last letter to give $w$. This proves the source
inverse without observing off-source geometry or a table archive.

For its actual-image direction, the finite tests are explicit. Check
finite ordered support and ABT grammar, the phase-dependent focus
condition and $D_p$ domain (or the inherited case), and the decidable
$j$-ancestry image. Check the acquired old-leaf and label condition.
Execute the recovered completed word and the indicated current prefix,
using the decreasing word cursors or inherited finite cursors to locate
it. Reject if the prescribed position is not attained, or if the
reconstructed support and receipt differ. All searches here are bounded
by those finite transactions and the finite indicated current transaction;
there is no search over future inputs or arbitrary histories. Every
accepted candidate re-observes to the supplied datum, and every attained
datum passes by (ER.71) and Lemma 17.3. This proves both identities for
$S_\mu$.

For boundary, each active source is a finite full rooted tree at every
cut, regardless of detached allocations. Every source position extends
an actual terminal position. Therefore its support is the prefix closure
of its terminal antichain, and the antichain is the set of maximal
support positions. Apply the source decoder to this independently
recovered support. Re-taking maximal positions proves the observation
identity as well, giving (ER.73) for $B_\mu$ separately.

For memory, the actual held anchor is $\mathsf A(x)$ inside every
fragment. Its addressed rows reconstruct $x$ directly; ancestry and
Lemma 17.3 give $u,w$ and the unique fine cut. The inherited phases
before Bind likewise retain $x$; after Bind they have the actually
acquired $\mathsf A(y)$, and the pending command removes the last
ancestry letter. Ready and Tail use the live $x$ case. These are all
roles of Definition 11.4, including the interval when the replacement
is partial or complete but not yet bound. Execution reconstructs the
same actual anchor contents, role and receipt. Finite replay/re-observation
as above tests its image and proves (ER.73) for $M_\mu$ without adding
retired tables or chronology to that observation.

For time, the actual initial addressed truthful replies determine the
finite installed $u$. The added 24 initialization opcodes have one fixed
order and no independent inputs. Thereafter the recorded input bits and
every actual row opcode/reply/operand record specify precisely a finite
prefix of the declared deterministic transition relation. Execute that
prefix and check each record against its actual operands and reply.
It reconstructs $w,f_\mu,J_\mu$ and re-observes the same chronology.
Conversely recording that reconstruction gives exactly the supplied
actual occurrence chain. No endpoint snapshot is needed. This proves
(ER.73) for $T_\mu$. All four reconstruct the same actual history,
including every retained record and reference identity. $\square$

## 18. Complete fine behavior, completed comparison and one-run charges

**Theorem 18.1 (individual task kernels and lawful recovery routes).**
For each individual $V\in\{S_\mu,B_\mu,M_\mu,T_\mu\}$ and all
$h,k\in\mathcal H_\mu$,

$$
 V(h)=V(k)\quad\Longleftrightarrow\quad h=k
       \quad\Longleftrightarrow\quad h\sim_{Q_\mu}k.
\tag{ER.76}
$$

All twelve recoveries between actual view images have opposite inverses,
agree along every route and preserve lawful/disabled domains, actual
readouts, the full responses (ER.70), complete successors and every
finite lawful adaptive continuation.

Proof. Theorem 17.4 proves each individual diagonal history kernel.
For clarity check both task inclusions separately. Equal source views
give the same history by the source inverse, hence identical present
readout, domains, complete responses and successors. Conversely equal
$Q_\mu$ profiles include equal actual acquired anchor, role and receipt;
the proved memory inverse gives the same history and thus the same
source support and receipt. Equal boundary views give the same history
by prefix closure and the separate boundary inverse, hence identical
responses; equal task profiles give the same memory-decoded history
and consequently the same terminal boundary and receipt. Equal temporal
views reconstruct the same initialized execution, so give identical
responses; equal task profiles again fix the same history and its unique
actual chronology, giving equal temporal views. Equal memory views give
the same history by the independent memory inverse and hence the same
responses; the reverse inclusion is immediate from the task's present
readout. None of these reverse inclusions uses the hidden full-successor
coordinate to separate histories, and no intersection of kernels replaces
an individual equality.

Let $R_{VW}=W\circ d_V$. On the actual images (ER.73) gives

$$
 R_{WV}R_{VW}=\operatorname{id},\qquad
 R_{WZ}R_{VW}=R_{VZ}.
\tag{ER.77}
$$

For action $a$, its view-domain is exactly the image of controls where
Definition 16.6 enables it. Decode a view, take that same actual action
with its actual owner/operand/reply, then observe its successor. Theorem
17.1 and the inherited acquisition proof ensure that successor is attained.
Every route therefore uses the identical row, event/completion/output
append and full $J'_\mu$. Thus, with equality of domains,

$$
 R_{VW}A_a^V=A_a^W R_{VW},\qquad
 \operatorname{Resp}_a^W R_{VW}=\operatorname{Resp}_a^V.
\tag{ER.78}
$$

Disabled trials on either route return the same none without execution.
Induction proves compatibility of finite continuations. In an adaptive
experiment the identical acquired response selects the same next branch,
so the same induction applies. These are finite mathematical algorithms
on actual view descriptions; the equations confer no new access right
or installed historical conversion service. $\square$

**Definition 18.2 (completed comparison and identity correspondence).**
Call a continuing cut a comparison cut when it is outside the interior
of a replacement fragment: inherited cuts and the entry/exit Edit cuts
are included. Contract each entire $E_0$-to-CellDone fragment to its one
Edit step and leave inherited rows unchanged. For a comparison prefix
$h$ denote this contracted ER11 prefix by $c(h)$.

Fix a coarse occurrence realization of Assumption 11.1 that allocates
each replacement tile in the preorder of Definition 16.1, retains the
old tile, and uses the same snoc backing for inherited words. The
coarse Edit event carries its acquired row/address/label and old/new/next
operand binding; this is the bounded event convention of Definition
11.3, with the binding made explicit. A coarse Edit performs its
positioning and guard work inside its old atomic boundary. It has no
forward-reversal cells or fine bank. Numerical fresh names need not
agree between the two realizations.

The identity correspondence $\iota_h$ maps initial source occurrences
by initial position, inherited new occurrences/rows/words by their
creation roles, and every replacement node by (its U transaction,
original leaf, literal target position). Old tile occurrences keep their
previous correspondence when retired. Each inherited event corresponds
to that same row's actual event; each coarse Edit event corresponds to
the one CellDone completion cell. Row/address references in those events
are transported by their creation-role correspondence, not by equality
of numerical allocation names. Field projections of that completion cell
give precisely the stated operand binding. Only event payloads have this
common-field correspondence: a coarse chronology predecessor is the
preceding contracted event, whereas a fine chronology predecessor is the
preceding actual fine event. Completion-chain predecessors form a third
specified chain. Their different link fields are retained explicitly in
the residual; no equality of these three predecessor fields is asserted.
The coarse chain is reconstructed from the contracted occurrence order.
This is a correspondence of
actual occurrences and fields, not an assertion of literal whole-state
equality.

The fine residual $\mathcal R_h$ retains the following complementary
actual data: the bank holder, slot cells, all slot/head values and extended
control; all invocation and retirement cells and their fields; every
forward word cell; every extra fine event with its actual references;
the exact fine chronological chain, including initialization and every
CellDone event; all completion-chain links; all fields of shared objects
not in the coarse projection; and the fine allocation order/names and
reference correspondence $\iota_h$. Every inherited retained object,
including old tables, input/output backing and retired occurrences,
belongs to the common projection or is explicitly retained in this
residual with its actual fields. Null fields, retired roles, both local
head values and the cleared bank values are included. The residual is a
typed partition of actual material and its remaining fields, not a new
state supplied to the running owner. Its mathematical use changes no
retention or cost.

**Proposition 18.3 (residual-preserving completed comparison).** At every
comparison cut $h$, contraction gives an attained coarse prefix $c(h)$.
The active labelled source, held/live anchor, original leaf frontier,
inherited acquired replies, output frames and one completed Edit binding
per finished fragment agree under $\iota_h$. The augmented comparison

$$
 J_\mu(h)\longmapsto
       \bigl(J_\partial(c(h)),\iota_h,\mathcal R_h\bigr)
\tag{ER.79}
$$

preserves every actual fine material/record/reference component and has
an inverse on its actual image. It claims neither literal equality
$J_\mu=J_\partial$ nor an original-Q action at an interior fine cut.

Proof. At the first Ready the actual sources and acquired anchor values
agree; the extra initialization and bank are retained in $\mathcal R_h$.
An inherited row has the same acquired operands, replies, source/table
values and outputs, with references transported by creation role.
For a fragment, Theorem 17.1 gives exactly the coarse tile replacement,
retained old tile and once-advanced original cursor. CellDone alone
provides its completed operand binding. The literal target positions
establish a bijection of the new tile nodes. Thus induction over contracted
rows proves the assertion and all role correspondences, including later
retirement of previously created nodes and anchor replacement.

For the inverse in (ER.79), instantiate common objects using their
$\iota_h$ names and common fields, restore their residual fields, insert
each complementary typed object with its retained actual fields, and
restore the fine root/head/slot/control values, exact chronology and
allocation order. Every fine object and field is in one of these specified
parts, so their disjoint typed union is exactly $J_\mu(h)$. Conversely
partitioning that union gives the same triple on the actual image.
In particular no fine record, address copy, invocation or cleared referent
is discarded. A coarse event chain is a selected comparison coordinate;
it is not substituted for the actual fine chain or its charges. A fine
probe, reversal or birth has its own successor and event and is not one
old Advance. This proof therefore supplies only the stated completed
comparison, consistent with the different interior task domains. $\square$

**Proposition 18.4 (same-fragment and same-run resource coordinates).**
Use exactly the atomic and backing convention of §§16–17. For a completed
fragment at an old leaf of depth $d$, let $n=n_\ell$, $m=m_\ell$ and
$g=g_\ell$. Its exact number of executed fine rows and fine events is

$$
 e(d,\ell)=8d+4n+g+3m+34
   =\begin{cases}8d+63,&\ell=\alpha,\\8d+87,&\ell=\beta.\end{cases}
\tag{ER.80}
$$

Its source/word coordinates include exactly $4d$ word-field reads,
$d$ forward-word births with $2d$ initialized payload fields, $d$ source
positioning follows, $g$ relative guard follows, $3n$ old-node field
probes, $m-1$ staging vacancy probes, one attachment probe, $m$ template
births with $3m$ initialized fields, $m-1$ staging child writes and one
source publication. It retains all $n$ old tile nodes and all $m$ new
ones. In addition to inherited material, its total abstract cell births
are exactly

$$
 m+d+e(d,\ell)+3:
\tag{ER.81}
$$

one invocation, one retirement cell and one completion cell, besides
its template/word/event births. All bank, control, row/next/invocation
reads and assignments, record-tail access/retargeting, payload field
initializations and output/serialization costs remain included as their
actual separate coordinates; (ER.81) is a cell count, not a total fee.

Proof. The four entry rows contribute 4. Reversal has $d+1$ tests and
three other rows per letter, contributing $4d+1$; SeekInit contributes
1, seek has the same $4d+1$ form, and Locate contributes 1. Old-tile
guarding contributes $4n+g$ from resets, paths and three field probes.
Birth contributes $m$, the separate check/write links contribute
$2(m-1)$, and AttachCheck/Publish contribute 2. Retire/Next/Handoff
contribute 3, the 22 separate cleans contribute 22, and CellDone
contributes 1. Their sum is (ER.80).

Reversal reads last and previous separately, and seek reads letter and
next separately, giving $4d$ actual word-field reads. Their constructor
and source-follow counts are the stated ones. Every other source-field
coordinate follows directly from its fixed literal list. Source-node
initialization writes one tag and two child fields; later only the listed
links and publication change child fields. Each executed row creates
one fine record, and only the three indicated rows create the other
three descriptors. There are no other births inside this fragment in
the declared abstract basis, proving (ER.81). The invocation's three
later field assignments, seven CellDone field reads, actual entry/list
reads, 22 clears, all bounded reference/control updates and each event's
own fields/tail coeffects are separate work, regardless of cell count.

More explicitly, for any prefix define its resource vector by summing,
over its actual rows, the numbers of source/word/local field reads,
source/word/local field assignments, typed births, event/descriptor
initializations and reference/control changes specified by those rows.
Include holder/slot/head creation and inherited atomic coeffects as
well. Each summand refers to this same initialized run. A tariff may
weight these coordinates only after it is declared; there is no
cross-basis scalar total implicit in (ER.80)–(ER.81). $\square$

**Corollary 18.5 (whole-transaction coordinates and their scope).** For one
actual U from $x$ with alpha/beta old-leaf counts $a,b$, the template
births are $5a+9b$, retained old-tile nodes are $3a+5b$, and forward-word
births are $\sum_{p\in\operatorname{LeafPos}(x)}|p|$. The fragment event
sum is

$$
 \sum_p e(|p|,x|_p)=8\sum_p|p|+63a+87b.
\tag{ER.82}
$$

The continuing-primitive count (ER.54) for that transaction becomes

$$
 |\operatorname{code}(\mathsf U)|+9+4N(\rho x)+\ell(\rho x)
       +\sum_p e(|p|,x|_p).
\tag{ER.83}
$$

Graft transactions retain (ER.54). The initial bank adds its separately
specified 24 transitions and 24 events before first Ready. Literal Read
and submitted-letter totals (ER.53) remain unchanged: the extra field
probes are not literal Read opcodes. Local old-plus-new tile coexistence
is $n+m=8$ or $14$, in addition to the source exterior, anchors, all
previous retained material, words, descriptors, bank and records.
No total-cost improvement, bounded total memory, minimum receipt,
minimal generator basis or Pareto dominance over another carrier follows.

Proof. Sum the exact per-leaf lists, using every old leaf once by
Theorem 17.1. Replace the $\lambda(x)$ old Edit occurrences in (ER.54)
by their actual fragment lengths; all other rows are identical, proving
(ER.83). The extra rows issue no literal Reads and alter no logical
refresh schedule, proving the unchanged (ER.53). Retention and fresh
disjointness give the coexistence count. Finally $f_\mu$ has at most
two words of length $|p|$ and finite tags, but those words, reference
widths and event count have no uniform bound over this domain. Neither
the count nor a finite control description bounds total backing. These
are coordinates of the chosen relation, without an order comparison
against differently endowed reciprocal or tape operations. $\square$

## 19. Mathematical dependence and exact remaining domains

**Definition 19.1 (source-specific increment and supplier correspondence).**
Repository references used in §§16–19 designate their source text at
$\texttt{540144ad9f007216b8dbf033784728d379dd013a}$.
The new mathematical content is the directed acquired-old-leaf relation
(ER.71), its actual word/field/invocation schedule and unique attained
position through delayed handoff/completion, and the resulting four
separate source-only/boundary/acquired-memory/chronology inverses for
that relation. This is repo-derived synthesis. Single-node construction,
ordered context replacement, prefix closure, persistence, replay and
abstract kernel/route algebra are intermediate suppliers, not additional
new general theorems.

Theorems 9.3/9.5 supply unique attained entrance and command ancestry;
Theorem 10.2 supplies the exact marked inverse $D_p$; Theorem 11.5
supplies actual initial and logical acquisition, the held old leaf list,
and the unchanged phases. Theorem 12.2 supplies the individual-kernel
proof pattern and its explicit atomicity limit in Definition 12.6.
Sections 13–15 retain their exact old source fibres, information bounds
and stationary-interface limits; adding $f_\mu$ does not change their
claims about forgetting the old frontier. ABT Theorem 12.1 supplies
erased-$E$ decoding and its two-query acquisition law. Those inverse,
acquisition and route results are used within the new relation rather
than asserted again as its mathematical novelty.

The [Intrinsic Substitution Coordinates declarations][ERISC], including
`no_alpha`, `pair_image` and private `substitution_injective`, with
[their owning Scribe][ERISCB], supply the existing substitution grammar
and injectivity. [Native Full Source Producer][ERPROD], including private
`traverse`, `production_reads`, `stationary` and its [owning Scribe][ERPRODB],
supplies the actual initial stationary traversal with unbounded finite
workspace. Its proof-side unknown-subtree parameters are not runtime
operands. [NativeSerialMachine][ERNSM] supplies its local/Read/substitution
chronology and replay; [NativeSerialEffective][ERMUEFF] and its
[owning Scribe][ERMUEFFB] require an actual code realization equation
and preserve their stated trace erasure. They supply no directed field
operation or current maintenance right.
[TypedFiniteViewKernel][ERMUKERNEL] and its [owning Scribe][ERMUKERNELB]
start from independently specified readouts and partial labelled steps;
that abstract kernel result is not the construction of Definition 16.5.
At the current mathlib manifest pin
$\texttt{56a005855ea17e0b0958f73ec801ae140b0a1679}$,
[StateTransition, `Respects`, `tr_reaches`, `tr_eval`][ERMUSTATE]
requires related starts, positive matching fragments and its halt
condition. Its refinement machinery alone gives no cut inverse,
authority or resource equality here.

[SSA §13][ERSSA] supplies a positioned fixed-occurrence reciprocal
relocation and explicitly leaves operand acquisition, continuing permits,
control and records as separate premises. Its three-slot fixed-occurrence
lower bound excludes fresh directed carriers. [Open-row completion,
§§4–7][ERMUOR] supplies phase-first ownership, before-image binding and
conditional exactly-once completion; Theorem 17.1 establishes actual
enablement for these two ER tiles under the stated static owner, rather
than assuming the all-row native premises of that supplier.
[Single-vertex construction, §§2–7][ERMUSV] already supplies singleton
construction, local partial-tree inverses, a whole-carrier one-fragment
history theorem and conditional retained-record birth bounds. Its strong
history inverse observes whole storage/joint retained memory and does
not supply this ER source-only publication/frontier/completion join.
Its production bound remains applicable with its own disjoint-receipt
premises; (ER.81) counts event births as well as template births.
[Source-call recovery, §§7–8][ERMUSC] separates a completed comparison
from original interior task equality. Its rooted parent-first 49-cut
argument is not applied to detached staging; its complete-record
restriction is retained in (ER.79).

PR57's whole-array writeback keeps its source unavailable during that
writeback. The growing unary and paid-view atlases retain their
whole-storage observations, atomic row/patch and service/authority
premises. Their actual paid traversal/copy/record results remain
suppliers in those domains. No whole-storage observation, acquired seed
plus ordinal, or historical delivery service is substituted for the
selected observations (ER.72). This bounded synthesis makes no claim
of global absence or worldwide priority and uses no transfer from
unrelated arithmetic or rational-fibre results.

**Definition 19.2 (literature-attested intermediate constructions).**
Hassan, Mackie and Sato, *An Implementation Model for Interaction Nets*,
[primary text, §4 and Figure 4][ERMUNETS], gives explicit allocation
returning a held node reference and assignments to its ports. Its finite
right-hand-side construction is a literature-attested intermediate
analogue of detached known-template birth/link. Its freeing convention,
interaction ports and supplied interface do not give this model's
retention, acquired ER leaf, source inverse or owner capability.
Bennett, *Logical Reversibility of Computation*, [Introduction and
history/copy/reverse construction][Bennett], is the literature-attested
supplier for retained history as paid extra storage and work. No
thermodynamic conclusion, free record, automatic historical service or
reverse operation on this source is inferred. The context interpretation
of Huet's *The Zipper*, cited in Convention 12.5, likewise retains its
focus/sibling/path premises; it does not supply (ER.74)'s old-source
recovery. These classical constructions are credited intermediate uses,
not new numbered results or claims of a new general pointer calculus.

**Definition 19.3 (remaining mathematical scope).** The model $\mu$ changes
only the occurrence representation, its explicitly endowed directed
field authority, fixed paid bank, address preparation and the refined
Edit/receipt/record relation. It retains all finite seeds, actual raw
acquisition and $E(j(u))$ initialization, all lawful continuing bit
prefixes, every selected original old leaf, same source/owner/orientation,
held/live acquisition and complete retained material. It does not supply
a successful old-tile guard as an oracle; that guard is proved in
Theorem 17.1. It supplies finite internal selection and continued local
anchor use, not a new unknown-input disclosure.

The four-kernel domain begins at first Ready. Finer cuts inside initial
acquisition/initialization, one-node initialization, event/descriptor/
reference coeffects, literal Read suffix construction, known preparation/
graft and Bind remain outside it. Reciprocal parent maintenance,
individually split reciprocal endpoints, native installation and current
native maintenance admission/return remain separate models and
obligations. There is no result for concurrent writers, changing rights,
independent Busy requests or arbitrary owner services. Mathematical
source/boundary decoding does not install acquisition, serialization,
authenticated named-historical selection, cross-owner handoff, callable
conversion or returned delivery of arbitrary fine views.

The completed comparison preserves all fine residual material and its
actual identities; it does not identify an interior Advance with an old
Advance or provide original-Q interior transport. Every prior fixed-
$G_{gc}$, original-$Q$, parked-consumer, unchanged-initialization and
original-authority claim keeps its exact scope. Open problem 8.1,
the original prediction task (ER.3), its $M_1(D)$ and sharp/effective
certification questions remain as stated. Coherent infinite realization,
general generator/resource minima, universal alpha/beta reduction,
physical space/time interpretation and the full four-expression objective
are not consequences of this finite directed theorem.

[ERMUEFF]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.lean
[ERMUEFFB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.scribe.cs
[ERMUKERNEL]: ../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean
[ERMUKERNELB]: ../../../Blueprint/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.scribe.cs
[ERMUSTATE]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/StateTransition.lean
[ERMUOR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OPEN_ROW_COMPLETION_AND_AUTHORITY.md
[ERMUSV]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SINGLE_VERTEX_CONSTRUCTION.md
[ERMUSC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SOURCE_CALL_TASK_RECOVERY.md
[ERMUNETS]: https://arxiv.org/html/1505.07164v1

## 追加锚（本行以下为增补区）

## 20. A current spatial body as the actual operand supplier

**Definition 20.1 (the directed received-shape model).** Denote by $\nu$
the following model. Retain $\mathcal T,E=\rho^2,j,F_w$, the compound
logical sources of Definition 16.1, the directed occurrence fields and
static exclusive owner of Assumption 16.2, canonical fresh allocation,
retention and the fine Edit relation of Definition 16.5. Fix the owner
$o$, root **port** $\pi$, orientation, public finite control and typed
allocation order before choosing any seed or input. The reference in
$\pi$ may change at a graft; $\pi$ and its owner do not change.
All finite $u\in\mathcal T$ and all finite words in
$\Lambda=\{\mathsf U,\mathsf L,\mathsf R\}$ are admitted.

Retain the actual raw acquisition of installed $u$, preparation of
$a_0$, startup graft and two warm-up substitutions. Thus the initialized
source is the actual $E(j(u))$. Retain the bank of Definition 16.3,
its initialization and its event conventions. Replace **each** logical
acquisition, including the first, by Definitions 20.3–20.5 below. The
new service constructs its replacement rows directly; the Read0,
Read1, Replace0 and Copy controls of Definition 11.3 are not part of
this model. Bind, lookup, output and continuing actuation have the
correspondence specified in Definition 20.6. Earlier models retain
all their own operations and hypotheses.

The sender and receiver are two control roles of this same owner. They
have distinct buffers; passing a value between them is an actual
mailbox operation. There is no independent service request, historical
selector, writer, revocation, interruption, scheduling input or freely
chosen waiting occurrence. A prescribed Advance performs the next row;
stopping a finite prefix performs no further row. Input is admitted
only at the two inherited command-input controls. A service therefore
has no independent choice to be retained at a returned cut.

**Assumption 20.2 (local material and bounded operation boundary).** In
addition to the inherited bank, install one holder with twenty reference
slots

$$
D,W,n,l,r,h,t,s,H,K,v,d,q,C,c,Z,z,f,g,e
$$

and four finite latch slots for token, side, pattern and service phase.
The holder and its twenty-four one-value slot cells are created and
attached in a fixed order, all slots initially null. This takes
exactly twenty-five bounded creation rows with their events. Slot roles
are reused between nonoverlapping service phases. The inherited
current-anchor root holds the current descriptor; its tableHead and
leafHead resolve the two list roots. These references, mailbox
value/state and finite control are actual retained local material.
The mailbox value/state are two of the finite latch roles, reused after
delivery. No moving cursor is
an immutable part of the public code.

A local cell has one of the following bounded payloads: source work
$(\mathsf{node},\mathsf{next})$; received word
$(\mathsf{token},\mathsf{next})$; shape node
$(\mathsf{tag},L,R)$; pending slot
$(\mathsf{parent},\mathsf{side},\mathsf{next})$; materialization work
$(\mathsf{shape},\mathsf{address},\mathsf{next})$; addressed row
$(\mathsf{address},\mathsf{label},\mathsf{next})$; leaf link
$(\mathsf{row},\mathsf{next})$; or the snoc address cell of Definition
16.3. A service descriptor has ten fields

$$
(o,\pi,\mathsf{sourceRoot},\mathsf{entry},\mathsf{bodyHead},
 \mathsf{bodyTail},\mathsf{shapeRoot},\mathsf{tableHead},
 \mathsf{leafHead},\mathsf{state}).
\tag{ER.84}
$$

Here entry is the actually held chronological tail at service entry,
not a supplied integer. The other references are obtained by the
operations below. State ranges over receiving, sealed, parsed,
materialized, live, held and returned. Its meaning includes its control
phase; returned is live for subsequent current-table use.

Each indicated field read, child follow, field assignment, reference
or finite-tag test, allocation, input or output is a row. Its bounded
bank/control assignments and one event have the conventions of
Definition 16.4. Creating a cell initializes its listed fields; those
initializations are charged. Appending one cell may assign the previous
tail's one next field and the two head/tail references as bounded
coeffects, with all three assignments charged. Pushing one stack cell
and changing its head is likewise bounded. A pop reads its fields in
their displayed order and then changes the head. When several reads,
tests, births or assignments are named together below, they are performed
in that order, one row each; no list traversal is one row. A fixed
finite branch selects a fixed finite row sequence. These rules define
finite control with unbounded finite linked data, not bounded storage
or fixed-width references.

All rows append their opcode, actual operands, acquired value and bounded
assignments to the actual event chain. Cleared or retired material stays
allocated. No event payload, previous descriptor payload, old table,
old leaf-list content or raw-seed acquisition supplies a traversal,
parser or materialization operand. Bind may retire held roots without
reading their contents. Their retention is part of the joint state,
not an alternative operand source.

**Definition 20.3 (actual spatial delivery).** For a finite unlabelled
full shape $G$, let $\kappa(G)$ be its preorder word over
$\{\mathsf b,\mathsf d\}$: $\mathsf d$ for a terminal and $\mathsf b$
followed by its left and right words for a branch. This is a notation
for a spatial body's codec; neither the tree nor its word is supplied
to the sender as an argument. Terminal labels are erased.

Service entry reads the actual reference in $\pi$, creates (ER.84)
with that sourceRoot, actual entry tail and empty output fields, and
pushes that reference on an initially empty source-work stack. The
source is stationary until materialization and Bind finish. Delivery
repeats the following finite operation sequence.

| Control role | Actual operation and continuation |
| --- | --- |
| Work test | Test the source-work head. A nonempty head is popped into the node latch. Empty work goes to End only after the preceding mailbox acknowledgement. |
| Source observation | Probe that node's actual tag. A branch latches $\mathsf b$, follows its nonnull left and right fields, and pushes right then left. Either terminal tag latches $\mathsf d$ and pushes nothing. |
| Offer | With empty mailbox, write the latched token and mark it offered. The next control is Take; the sender cannot advance its traversal. |
| Take | Read the actual offered value into the receiver latch. |
| Arrival | Allocate one receiver-owned word cell containing that latch and a null next field, and append it to the receiver list. |
| Acknowledge | Clear mailbox availability to empty and leave this token's delivery controls. Return to Work test. |
| End | With work and mailbox empty, set the descriptor's body endpoints to the actual receiver endpoints, set state sealed and enter the shape parser. |

The word cells contain only the spatial tokens and their next links.
In particular they contain no source-node references, labels, addresses,
seed, command word or separate source-state payload. The descriptor and
events retain the causal source binding separately. There is no source call between
an Offer and its acknowledgement, and there is exactly one Arrival on
that control path. End is a paid control occurrence, not a missing-token
inference by a clock. The sender's stack, tag probes and follows, every
mailbox operation, allocation and end check are charged.

**Definition 20.4 (received shape materialization).** Clear the local
shape-root slot. Push its distinguished root-slot reference on a pending
slot stack, and set the word cursor to the descriptor's sealed bodyHead.
A nonroot pending slot specifies a held shape parent and one literal
side. For each received word cell, read its token and next reference,
require a pending slot, and pop that slot. Allocate one fresh shape node
with that token as tag and null children, then assign the indicated slot
to its returned reference. For $\mathsf b$ push its right slot and then
its left slot; for $\mathsf d$ push neither. Continue at the read next
word reference. Empty input with pending work, or nonempty input with
no slot, takes the fixed fault control. Successful exhaustion requires
both empty input and empty slot stack. Only then set shapeRoot to the
actual constructed root, set state parsed and enter materialization.

This is the ordinary pending-slot parser for a full binary preorder
word, used as an intermediate construction. Each slot, tag, link and
input-cell access is material. A $\mathsf d$ node remains null on both
sides. A $\mathsf b$ node receives both children before successful
exhaustion. No operation tests equality of two unknown whole trees.

**Definition 20.5 (body-only address and label construction).** Start an
empty addressed-row list and empty leaf list. Push
$(\mathsf{shapeRoot},\varepsilon)$ on a materialization-work stack,
where $\varepsilon$ is the fixed empty snoc reference. Pop a held shape
reference $v$ and actual backed word $q$. Inspect the following bounded
pattern at $v$, by individual tag reads and child follows.

| Actual received pattern | Constructed row and new pending work |
| --- | --- |
| Root branch, both children terminal | Append $(q,\alpha)$ and its leaf link. |
| Root branch, left child a branch with two terminal children, right child terminal | Append $(q,\beta)$ and its leaf link. |
| Root branch, both children branches | Append $(q,\mathsf{branch})$; create two snoc cells extending $q$ by $L,R$; push right child with $qR$, then left child with $qL$. |

Any other pattern faults. The middle pattern must check both indicated
grandchildren; it cannot accept an arbitrary left subtree. The input
shape has already been completely constructed by Definition 20.4, so
its terminal tags have exactly null children. Pattern inspections touch
at most the root, its two children and two grandchildren. The address
stored in a row is precisely the actual snoc reference held on this
stack. Each next-row and next-leaf link is installed as the corresponding
row or link is appended. At empty work set the descriptor's tableHead
and leafHead to these actual heads, state materialized, and enter Bind.
No acquired row, address or leaf link from before this service is shared,
except the fixed empty-address sentinel.

The three cases are the existing erased-$E$ grammar of ABT Theorem
12.1, applied here by finite local operations to the **received** shape.
The actual row constructor receives no logical tree argument. Its only
variable data are these shape nodes, its own work stack, the snoc words
it constructs and its partially constructed lists.

**Definition 20.6 (command, binding, return and complete state).** At Bind,
retire the previous table and leaf list, install the materialized
replacement and its descriptor as the current anchor, and mark it live.
Run exactly the inherited local $LL$ lookup and framed table output.
Replace Finish by Return: retire remaining active service scratch,
clear its twenty-four service slots and the inherited command/reply/result
latches by a fixed finite sequence, then mark the current descriptor
returned and enter Ready in the final row. Cleanup uses no unbounded
scan. Each clear is charged. No earlier service control is Ready.
Startup uses the same service, lookup, output and Return with its startup
tag; the domain begins only after this actual first return.

Ready and Tail receive the actual code $\mathsf U=0$, $\mathsf L=10$,
$\mathsf R=11$ of Definition 11.3. Select marks the receiver-derived
anchor held. For U it sets the cursor to that anchor's actual leafHead.
Every nonterminal Edit executes Definition 16.5, including its $E_0$,
$E_1$ and $E_2$ reads of this leaf link, this row and this row's address
and label. SeekInit uses the actual current reference in $\pi$.
Edit at $\top$ enters the new service. For L or R retain the actual
known-$A$ preparation and corresponding graft; its successor enters
the same service. There is no inherited logical-refresh acquisition or
old-table fallback. New leaves born during U never join its old list.

Let $J_\nu(u,w)$ denote the complete joint state after the return for
$w$, including $w=\epsilon$ at startup. It includes the live source,
all retired/detached occurrences, raw and logical acquisition material,
all delivered words, received shapes, rows, address/stack backing,
descriptors, bank/holder/slot material, actual references, allocator,
finite control, input/output and chronological records, and fixed rights.
All references are canonical consequences of this initialized execution.
There are no independent name, preparation or source-layout choices.
The task $Q_\nu$ at such a cut has the present acquired table and local
$LL$ result. Its three legal actions are the complete coded command
transactions, including all prescribed intervening rows. Its response is

$$
\bigl(a,\mathsf{legal},\mathsf{ok},C',\operatorname{lookup}_{LL}(C'),
       \Delta\Gamma_\nu,\Delta\mathsf{Out},J'\bigr).
\tag{ER.85}
$$

$J'$ is the complete original successor just specified, not an emitted
snapshot. All finite command responses, including their legal domains,
are compared; other action symbols have the fixed disabled value and
no executing successor. The internal row record in (ER.85) retains every
actual guard, delivery, acknowledgement, binding, output and return.

## 21. Authentic operand use, exact admission and continued return

**Theorem 21.1 (received spatial operands actuate the current source).**
For every finite $u$ and every finite admitted $w$, the schedule of
§20 reaches exactly one returned-command cut $J_\nu(u,w)$. At this cut,
with $x=F_w(j(u))$, the current source is $E(x)$ at the fixed owned port,
and its current table is the actual $\mathsf A(x)$ materialized solely
from the body delivered in its last service. That body is exactly

$$
\kappa\bigl(\operatorname{sh}(E(x))\bigr).
\tag{ER.86}
$$

For every next U, its complete old-leaf address and label operands are
the fresh materializer's actual cells. Every source walk, old-tile guard,
staging test and attachment test succeeds. The resulting source is
$E(\rho x)$, the next service acquires its spatial body, and lookup,
output and exactly one Return complete. L and R similarly give
$E(Lx)$ and $E(Rx)$ and a next authentic returned table. These assertions
are uniform over all finite seeds and all finite command words, with
completion conditional only on supplying their specified bits and
Advances.

Proof. During one service, the pending source stack lists actual
unvisited roots in left-first order. Initially it contains exactly
the reference read from $\pi$. At a branch, following both actual child
fields and pushing right then left replaces its pending subtree by
its two children. A terminal contributes no children. Induction on a
finite source subtree proves that it contributes exactly its preorder
word and visits each of its nodes once. Source tags are read before
erasure. Stationarity and exclusive ownership preserve the pending
references; no body content is obtained from an old table. This is the
ordinary traversal invariant underlying NativeFullSourceProducer's
private `traverse` and `production_reads`, here with actual directed
reference follows rather than an assumed root-address primitive.

After $i$ acknowledgements, the receiver word has exactly the first
$i$ offered tokens in order and the mailbox is empty. Offer, Take,
Arrival, Acknowledge prove the next case: the only appended token is
the value read from that mailbox, and control leaves Arrival before
another token can be offered. There is neither duplication nor a
silent bypass. End is reached precisely after the finite traversal
and the last acknowledgement. Hence its sealed body is the actual
spatial word of the same stationary sourceRoot in (ER.84).

For the parser, the pending slots are exactly the unfilled child
positions in left-first order. Each consumed token fills its first
slot, creating just the two new slots prescribed by a branch. Structural
induction on a full shape shows that its preorder word consumes one
initial slot and leaves none for that subtree. Thus the authentic body
fills the root slot, exhausts both lists and constructs precisely
$\operatorname{sh}(E(x))$ in fresh receiver material. No future token
is assumed at a partial cut.

Apply ABT Theorem 12.1 only as the following intermediate grammar law.
At a logical alpha its shape is the first pattern of Definition 20.5;
at beta it is the second; at a logical branch it has two encoded,
branch-rooted children and is the third. These patterns are disjoint.
Induction on the logical tree, with proof-side address $q$, shows that
materialization appends exactly its preorder addressed rows, leaf links
and labels. In the branch case the two new actual snoc cells spell
$qL,qR$, and the two child-work cells preserve that invariant. The
induction proves that every old-leaf operand is backed before Bind;
it is not an unexecuted application of an abstract inverse. All loops
consume a finite received list or a finite tree frontier, so all three
phases terminate. Bind obtains $\mathsf A(x)$ with its actual new leaf
list and truthful current-source binding.

Startup has actually established $E(j(u))$, so this argument establishes
the first returned table without source-dependent advice. Suppose the
assertion holds for $w$. Until Select there is no writer. For U, $E_0$
reads the leaf link created by the last materializer, $E_1$ reads its
row's newly constructed word reference and $E_2$ reads its decoded
label. The actual list equals the original leaves of $x$. Their
addresses are nonempty and prefix-incomparable. Earlier publications
therefore preserve each later old tile $C_\ell$ and its proper-prefix
context. The word reversal, positioning, bounded guard, fresh birth,
link and publication argument of Theorem 17.1 applies with these exact
new row references as its initiating operands. In particular its
successful-guard premise is proved by the received-body invariant;
no successful-test bit is supplied. Each completed fragment changes
exactly one original tile and advances once. At $\top$ the source is
$E(\rho x)$. For a graft the prepared known $A=E(\alpha)$ and its
orientation give the corresponding equation by (ER.33). These operations
are at the same $\pi$ under the same live capability throughout.

The next service is now on precisely that actual successor. It constructs
a fresh current table before lookup/output. Every inherited output row
terminates on this finite table. Cleanup is finite. The only edge entering
Ready is the final Return; its predecessor leaves that edge, clears the
pending command and cannot execute it again without another supplied
command. No delivery, acknowledgement or Bind returns to Ready. Induction
on $w$ therefore gives existence, unique attained returned position and
exactly one command return per completed command. Finite descriptive
execution also determines every retained cell and event identity. This
is an attained-position proof for the returned-command domain, not a
classification of the service's interior positions. $\square$

**Theorem 21.2 (exact leaf-driver admission at a fixed owned port).**
Let $x,y$ be arbitrary finite compound logical trees. Suppose the
current source at $\pi$ is the canonical directed $E(y)$, the stated
static owner right is live, and a materialized received body supplies
exactly the complete leaf list of $\mathsf A(x)$. Run the U leaf driver
of Definition 20.6 on that list, stopping at its first failed path or
tile test. All its leaf publications complete if and only if $x=y$.
When they complete the resulting source is $E(\rho x)$. This is an
exact **whole-driver success** criterion, not atomic rejection of an
incorrect $x$ and not an authentication test for a foreign descriptor.

Proof. If $x=y$, the incomparable-leaf argument in Theorem 21.1 gives
all tests and the stated endpoint. Conversely enumerate the leaves of
$x$ as $p_1,\ldots,p_m$. A publication at $p_i$ changes only that tile's
attachment and subtree. For $j>i$, $p_i$ and $p_j$ are incomparable,
so it changes neither the path to $p_j$ nor its subtree. Thus, if the
entire driver succeeds, every path and guard observed at $p_j$ would
have succeeded on the initial $E(y)$ as well. Its exact tag and both
child-status checks require

$$
E(y)|_{p_j}=C_{x|_{p_j}}=E(x|_{p_j})
\quad(1\le j\le m).
\tag{ER.87}
$$

Here existence of every proper path is part of success. The leaves of
a finite full $x$ are a complete prefix code for its own branching
skeleton. Induction on that skeleton reconstructs $E(y)$ from the
subtrees in (ER.87): at an internal node both required child paths
exist, and at a leaf the displayed complete subtree is fixed. Hence
$E(y)=E(x)$. Injectivity of $E$, supplied by the substitution or ABT
inverse, gives $y=x$. Notice that an individual test need not say that
$p_j$ is a logical leaf of $y$; the complete covering family is what
forces equality.

For an explicit late failure, take $x=\langle\alpha,\alpha\rangle$
and $y=\langle\alpha,\beta\rangle$. The first test at $L$ succeeds
and publishes $B$ in place of $A$. The test at $R$ subsequently rejects
$B$ against the required $A$. The first published change and its records
remain. Thus the equivalence cannot be strengthened to rollback or
no-write rejection. Rights and the fixed port were independent hypotheses
in both directions; equal body values issue no capability. $\square$

**Proposition 21.3 (operand dependence and authenticity are different).**
In $\nu$, the address/label read dependency of every U fragment runs
through the last received word, its parsed shape, its fresh snoc/row
constructors and its actual leaf link. No old anchor, sender table,
chronological replay or public dictionary supplies an alternative operand.
For any finite compound $z$, supplying the canonical word
$\kappa(\operatorname{sh}(E(z)))$ to the same local parser/materializer
constructs exactly $\mathsf A(z)$; at a current $E(y)$ the whole U driver
then succeeds exactly for $z=y$, under Theorem 21.2's rights assumptions.
This counterfactual dependence does not make the supplied word an
authentic current-source acquisition.

Proof. The variable reads in Definitions 20.4–20.5 are exhausted by
received-cell, local shape, own stack and own partial-output reads.
The only literal label choices are the three disjoint shape cases.
Every nonempty row address is constructed by one of their actual snoc
extensions. Definition 20.6 binds only this output and directs $E_0$–
$E_2$ to it. The intermediate ABT induction of Theorem 21.1 gives the
counterfactual table for every $z$, and Theorem 21.2 gives its exact
success domain. Erasing the receiver list and its constructed material
therefore removes the only declared path to those operands; even the
empty address sentinel supplies no leaf label or leaf-list entry.

The stronger authenticity assertion in Theorem 21.1 instead uses actual
root capture, source probes, mailbox arrivals, seal and stationarity
through Bind. A different source with equal value can supply equal
words without that chain or a right at $\pi$. Likewise a truthful old
body can become stale after an intervening writer in a different model.
Neither equality nor parsing rules out those cases. The no-writer and
same-owner hypotheses rule them out on $\nu$'s actual runs. $\square$

## 22. Four separate recoveries at all returned-command cuts

**Definition 22.1 (independent returned observations).** On
$\mathcal H^{\rm ret}_\nu=\mathcal T\times\Lambda^{<\omega}$ take
these four projections of the actual $J_\nu(u,w)$.

| View | Actual selected content |
| --- | --- |
| $S_\nu$ | The current source's ordered unlabelled support at $\pi$, with no service/workspace/record support attached. |
| $B_\nu$ | That source's uncoloured terminal-address antichain. |
| $M_\nu$ | The current receiver-materialized addressed rows, including their current fixed $o,\pi$ binding and local-use right. No old table, body, descriptor-entry reference, root-allocation name, seed, ordinal, past command word or history is an extra observed field. |
| $T_\nu$ | The ordered actual occurrences from installed-source entrance through this Return, including initial truthful raw acquisition, supplied command bits, actual field probes, mailbox operations, materialization, actuation, outputs and returns. No endpoint snapshot is appended. |

The memory equality convention compares complete addressed contents and
fixed binding/right, as in Definition 11.4. Actual descriptor and backing
identities remain in $J_\nu$; they are not hidden clocks in $M_\nu$.
The spatial body (ER.86) is a codec of the independent source support:
terminal/branch status is determined by that finite full support. It
contains no record or execution index. Serializing any of these views
or running a recovery computation costs additional work. The installed
service delivers this current S-body, not arbitrary T-, B- or M-bodies.

**Theorem 22.2 (individual kernels, attained return and route agreement).**
For each $V\in\{S_\nu,B_\nu,M_\nu,T_\nu\}$ separately and every
$h,h'\in\mathcal H^{\rm ret}_\nu$,

$$
V(h)=V(h')\quad\Longleftrightarrow\quad h=h'
 \quad\Longleftrightarrow\quad h\sim_{Q_\nu}h'.
\tag{ER.88}
$$

Each view has a finite decoder on its attained image to the identical
complete $J_\nu(h)$. All twelve same-cut recovery arrows are mutual
inverses and agree along every route. They preserve (ER.85), including
its complete original successor, actual service/actuation records and
all finite returned-command dynamics.

Proof. Theorem 21.1 establishes $r=E(F_w(j(u)))$. For $S_\nu$, erase
labels and use the existing ABT inverse, followed by Theorems 9.3/9.5's
unique $j$ entrance and ordered U/L/R ancestry. This returns exactly
$(u,w)$ without a service count or entry reference. For $B_\nu$, finite
prefix closure reconstructs the support, giving its separate decoder.
For $M_\nu$, its complete actual rows reconstruct the labelled logical
$x$, and $E(x)$ supplies the preceding support decoder. For $T_\nu$,
its initial raw acquisition determines $u$; its actual supplied bits
and completed Return controls determine the finished word $w$.
Theorem 21.1 proves that this last Return really was attained exactly
once for that command prefix. It is not inferred from an entry-test
program counter or an invisible service return.

Conversely $(u,w)$ determines the canonical finite schedule and all
four projections. Re-executing its **descriptions** reconstructs the
entire $J_\nu$, including received buffers, shapes, fresh word cells,
old retained anchors, fine invocation/completion material, actual
allocations, records, output and rights. There is no independently
chosen service count or interleaving left to recover. Replay is the
classical descriptive supplier here; it neither consults an unknown
source nor actuates a represented old right at the live port.

For the task inclusion from $S_\nu$, equal supports give the same
$(u,w)$ and therefore all equal responses. Conversely $Q_\nu$ equality
includes equal present acquired tables, giving equal $x$, hence equal
supports. For $B_\nu$, equal antichains give equal supports and responses;
conversely equal present tables give the same current tree and terminal
antichain. For $M_\nu$, equal contents recover the same $(u,w)$ and
responses; conversely present-table equality together with the fixed
current binding/right is exactly equal selected memory. For $T_\nu$,
equal occurrences give equal raw seed acquisition and completed input
word and hence responses; conversely equal present tables determine
$(u,w)$ by the source inverse, and its canonical execution determines
the same occurrence word. Thus both inclusions hold for each individual
view, without intersecting weaker kernels or copying history into them.

Write $d_V$ for these decoders to $h$. On attained images put
$R_{VW}=W\circ d_V$ and $A_a^V(V(u,w))=V(u,wa)$. Directly,

$$
R_{WV}R_{VW}=\mathrm{id},\qquad
R_{WZ}R_{VW}=R_{VZ},\qquad
R_{VW}A_a^V=A_a^W R_{VW}.
\tag{ER.89}
$$

Each path decodes the same $h$ and each successor is actually attained
by Theorem 21.1. Computing (ER.85) from this recovered $J_\nu(h)$
therefore gives the same legal domain, outputs, full internal append
and complete successor along every route. Induction gives the entire
finite response word. These algebraic steps use the ordinary typed
partial-step/kernel framework, not a new general recovery theorem.
No view map at an unreturned service interior is an argument of
(ER.88)–(ER.89). $\square$

## 23. Same-run resources and the precise mathematical increment

**Proposition 23.1 (charged receipt, backing and actuation).** Put
$x_i=F_{a_1\cdots a_i}(j(u))$ for an actual finite word
$w=a_1\cdots a_k$, and let $n_i=N(E(x_i))$, $N_i=N(x_i)$,
$\lambda_i=\lambda(x_i)$. Exactly $k+1$ spatial services occur, including
startup. For the service on $E(x_i)$, the following counts are exact:

$$
\begin{aligned}
\text{source tag probes}&=n_i,&
\text{source child follows}&=n_i-1,\\
\text{offered and arrived spatial tokens}&=n_i,&
\text{received word births}&=n_i,\\
\text{source-work births}&=n_i,&
\text{pending-slot births}&=n_i,\\
\text{received shape-node births}&=n_i,&
\text{materialization-work births}&=N_i,\\
\text{addressed-row births}&=N_i,&
\text{snoc-address births}&=N_i-1,\\
\text{leaf-link births}&=\lambda_i,&
\text{service-descriptor births}&=1.
\end{aligned}
\tag{ER.90}
$$

Thus its non-event cell births are exactly $4n_i+3N_i+\lambda_i$.
Every listed cell is retained, and its full bounded payload is initialized
and charged. Counts of event births equal the actual executed row count;
no event is a whole-body snapshot.

There are absolute finite constants $c_0,c_1$, independent of $u,w,i$,
such that the service through Bind, all its field operations and event
payload/tail coeffects use at most $c_0(n_i+N_i+1)$ rows and
$c_1(n_i+N_i+1)$ bounded field operations. The subsequent lookup uses
exactly $\ell(x_i)$ inherited lookup rows, output sends $N_i+4$ tokens,
and Return uses one fixed finite number of cleanup/return rows.
For each U beginning at $x_i$, the unchanged fine Edit fragments use
exactly

$$
\sum_{p\in\operatorname{LeafPos}(x_i)}
       \bigl(8|p|+63\,\boldsymbol1_{x_i|_p=\alpha}
                    +87\,\boldsymbol1_{x_i|_p=\beta}\bigr)
\tag{ER.91}
$$

rows/events, and have precisely the word, template, retained-old-tile,
invocation, retirement and completion coordinates of Proposition 18.4.
A continuing graft prepares three known source nodes and one new
attachment root. Input consumes exactly the actual one/two-bit command
codes. No logical-refresh literal query or suffix word is hidden in
(ER.90). Initial raw acquisition, initial supply and source initialization
remain additional paid work.

Proof. A finite full source has $n_i-1$ child incidences. The source
traversal visits each node once and creates one stack entry per visit;
its branch pushes account for all nonroot entries. Handshake induction
gives one received word cell per observed node. The parser fills one
slot per shape node, hence creates $n_i$ slots and $n_i$ shape nodes.
At each logical branch the materializer creates its two pending entries
and two address extensions. Together with the initial entry this gives
$N_i$ entries, $N_i-1$ words, $N_i$ rows and the stated leaf links.
Adding its one descriptor proves the birth formula.

For an explicit meaning of the constants, expand the finite row
sequences of Definitions 20.2–20.5, counting every field read, test,
birth and assignment. Let $b_s,b_p,b_m$ be the maxima of the lengths
of their respectively terminal/branch source-visit, terminal/branch
parser-visit and three pattern/materialization blocks, including their
loop tests. These are maxima of finitely many **fixed** lists: a source
visit uses one stack pop, one tag, at most two follows/two pushes and
four handshake rows; a parser visit uses one word read, one slot pop,
one birth/attachment and at most two pushes; a materialization visit
uses one three-field pop, at most five tag probes/four child follows,
one row, at most one leaf link or two word births/two pushes. None
contains a call to an unbounded local routine. Let $b_e$ be the length
of the fixed entry/end/phase-change/Bind sequences. The service row
count is bounded by
$(b_s+b_p)n_i+b_mN_i+b_e$; take
$c_0=b_s+b_p+b_m+b_e$. Let $b_f$ be the maximum number of field,
reference, finite-control and event-payload/tail accesses in any one
such bounded row, counting all its coeffects; take $c_1=b_fc_0$.
These definitions and the displayed block enumeration prove the bounds
without an unmeasured unit-cost whole decoder.

Lookup and output have exactly their inherited lists. Cleanup visits
a fixed set of slots, so it has constant length, and its last row alone
returns. Equation (ER.91) is the existing exact fragment count applied
to the actually materialized old leaves; no fragment is omitted at
refresh. The initial source producer makes $N(u)$ literal Reads, with
submitted-letter sum $\sum_{p\in\operatorname{Pos}(u)}|p|$, before
the actual known-$a_0$ preparation, startup graft and two warm-ups.
The inherited bank adds twenty-four creation rows/events and this
service holder adds twenty-five. The actual source installation,
code, rights, preparation, all old material and their records are
included by Definition 20.1. They are not absorbed into $c_0$.

For the whole run sum these coordinates over $i=0,\ldots,k$, add
(ER.91) exactly for its actual U commands, the actual graft preparations,
input, lookup/output/return and initialization coordinates. Equivalently
sum every declared field/birth/event coeffect over the actual row word.
Both descriptions count this single execution, including coexistence
of the old anchor, received word, parsed shape and new operands.
Reference width, source-operation internals at their inherited atomic
boundaries, serialization and any later descriptive recovery have their
own coordinates. No sum across different bases, physical unit-time
reference convention, total-fee comparison or optimality assertion is
implicit. $\square$

**Definition 23.2 (supplier correspondence and source-specific content).**
The mathematical increment of §§20–23 is the conjunction of actual
current-source spatial delivery, received-only materialized U operands,
(ER.87)'s exact whole-driver admission, continued same-port owned
actuation and returned-command recovery for this relation. It is a
repo-derived synthesis on the declared directed basis. The direct
source-table operand supplier of §§11/16 is replaced in $\nu$ by
(ER.86) and its receiver's new cells. Equality of values is used for
the admission theorem; actual provenance and rights are separately
established by Theorem 21.1's operation chain and Assumption 16.2.

Theorems 9.3/9.5/9.8 supply the unchanged entrance, ancestry and erased
source inverse. ABT Theorem 12.1 supplies the exact shape grammar;
its parsing law is an intermediate step, not a new numbered parser
result. Theorem 17.1 and Proposition 18.4 supply the exact directed
leaf fragment once its initiating row/word/label correspondence is
established. The new correspondence is to the receiver's own fresh
material, not merely to an equal old anchor. NativeFullSourceProducer,
including private `traverse`, `production_reads`, `stationary` and its
[owning Scribe][ERPRODB], supplies the stationary preorder/acquisition
pattern. Its runtime initial source is here the actual $E(x)$; unknown
subtrees used in the induction are proof parameters. The actual
reference traversal in §20 uses Assumption 16.2, rather than claiming
that the supplier adds directed field rights. IntrinsicSubstitutionCoordinates,
including private `substitution_injective` and [its owning Scribe][ERISCB],
supplies the injectivity used in (ER.87).

[Serial Literal Delivery, Construction 8.3 and Proposition 8.4][ERNUSLD]
already proves that received information can materialize the actual
subsequently consumed literal. Its task has a fixed finite menu
$\mathcal D_{H,J}$ and an installed immutable $R$ tail; neither its
menu bound nor its readonly backing is a uniform all-finite-seed
operand supplier for this changing source. Its `DelayedOriginalReadout`
`originalQueries` and private `original_query_bounds`, with the
[owning Scribe][ERNUDEL], retain their original suffix-query task.
The principle of actual receiver consumption is credited supply;
(ER.86)–(ER.87) concern a different current ER task.

[PVC §§6–7][ERPVC] supplies authentic paid finite historical conversion,
ACK/return and mathematical next-occurrence transport, with its stated
registry, binding and native installation. [Growing Paid View Cycle
§§7–8][ERNUGROW] supplies actual sourceBody consumption on its acquired-Zero
service domain. [RCA §§6, 11–16][ERNURCA] and [GCA §§5–6][ERNUGCA]
supply paid historical packages, acquired selectors, current invocation
rights and full Call return under their own premises. Their body,
source, owner, task and target correspondences are not inferred merely
from names. PVC Proposition 7.4 is not current private-source actuation;
RCA Proposition 6.5's missing-realization implication is not a no-map
theorem. None of these results is contradicted or restated as a universal
obstruction. No universal obstruction is asserted here.

TypedFiniteViewKernel and [its owning Scribe][ERMUKERNELB] supply the
abstract partial-response/kernel vocabulary. At the manifest's mathlib
revision $\texttt{56a005855ea17e0b0958f73ec801ae140b0a1679}$,
StateTransition `Reaches`, `Respects`, `tr_reaches` and `tr_eval` supply
ordinary finite-step/refinement language with their matching-start and
halt premises. They do not supply received-body acquisition or operand
provenance. NativeEffectiveSourceProducer's syntax decoder and
NativeSerialEffective's supplied code-realization equation likewise
confer no unexecuted local parsing, primitive realization or price.

McCarthy, *Recursive Functions of Symbolic Expressions and Their
Computation by Machine, Part I*, [§3, ordered-pair/list operations][ERNUMC],
supplies classical symbolic construction and recursive list processing.
Hassan–Mackie–Sato, [§4 and Figure 4][ERMUNETS], supplies classical
allocation returning actual references and port assignment. Bennett's
[Introduction and history/copy/reverse construction][Bennett] supplies
paid history and copying as ordinary computation resources. Full-binary
preorder parsing, depth-first traversal, finite linked stacks, prefix
closure, persistence, descriptive replay and the algebra in (ER.89)
are classical intermediate constructions, not claims of new general
results. The source-specific join in Theorems 21.1–21.2 and its actual
returned domain is the claimed increment, without a worldwide-priority
claim.

**Definition 23.3 (task-relative sufficiency and remaining domains).**
The $E$ code makes the received uncoloured body label-informative;
$j$ distinguishes the seed entrance and committed ternary ancestry.
Their supplied fixed-model classification is retained. The three
commands, root/owner capabilities and directed allocation/assignment
operations are explicit task/model premises, not consequences of the
two leaf names. The sender frontier is what discovers unknown source
nodes; received backing and snoc/leaf construction are what provide
subsequently used operands. The mailbox boundary prevents a sender's
unreceived table from standing in for that material. Full pattern and
path tests are what justify current actuation. Static exclusivity and
the mandatory schedule preserve the observed source until its use;
no authentication theorem for hostile replacement words is substituted.

Finite control supplies no uniform finite capacity: $n_i,N_i$, word
depths, retained earlier material and all event records grow with the
finite seed and word. The received word and parsed shape are sufficient
paid material for the stated provenance/task proof; there is no assertion
that every representation must retain both or that this schedule is
resource-minimal. No unrestricted history sidecar is added to S, B or M.
The chronological view observes actual operation order, not duration.

The recovery domain is exactly all completed returned-command cuts,
including the initialized empty-word return. There is no claimed
four-view inverse at a delivery return, partial received word, partial
parser/materializer, Bind, input Tail, guard, publication, cleanup or
other service/actuation interior. Those cuts retain actual control,
backing and events in the process but require their own sufficient
progress observations and attained-position proofs for any enlarged
recovery theorem. In particular this model's added service interiors
are not covered by $\mu$'s earlier fine inverse merely because the
leaf fragment is reused.

All earlier fixed-$G_{gc}$, original-$Q$, parked-consumer, unchanged-
initialization and original-authority obligations remain in their
original domains. No arbitrary historical or cross-owner delivery,
independent returning-service choice, callable arbitrary-view converter,
native/reciprocal/physical realization, infinite completion, universal
alpha/beta reduction, general generator minimum or physical spacetime
identification follows. The original prediction question (ER.3), Open
problem 8.1 and the wider four-expression objective retain their stated
unresolved scope.

[ERNUSLD]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_LITERAL_DELIVERY.md
[ERNUDEL]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.scribe.cs
[ERNUGROW]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GROWING_PAID_VIEW_CYCLE.md
[ERNURCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md
[ERNUGCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_CUT_ACQUISITION.md
[ERNUMC]: https://www-formal.stanford.edu/jmc/recursive/node3.html

## 追加锚（本行以下为增补区）
