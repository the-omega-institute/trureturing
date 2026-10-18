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
