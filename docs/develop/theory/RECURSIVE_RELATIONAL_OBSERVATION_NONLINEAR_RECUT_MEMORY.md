# Recursive relational observation: nonlinear recuts, predecessor context and retained memory

## 1. One finite relation and its strict supplied actions

**Definition 1.1 (fixed-length source and actual prefixes).** Fix a finite
nonempty alphabet $A$, put $q=|A|$, and fix $n\ge0$ and a nonempty relation
$C\subseteq A^n$. Concatenation is ordered, and $\epsilon$ is the empty word.
At cut $0\le k\le n$ let

$$
P_k=\{u\in A^k:\exists f\in A^{n-k},\ uf\in C\},\qquad
R(u)=\{f\in A^{n-k}:uf\in C\},\qquad
\mathcal R_k=\{R(u):u\in P_k\}.
$$

Thus $P_0=\{\epsilon\}$, $P_n=C$, $R(\epsilon)=C$, and every member of
$\mathcal R_k$ is nonempty. For a language $S$ and word $t$ define

$$
\partial_tS=\{f:tf\in S\},\qquad
\operatorname{Pref}_d(S)=\{t\in A^d:\partial_tS\ne\varnothing\}.
$$

In particular $\partial_\epsilon S=S$ and
$\partial_{ta}S=\partial_a(\partial_tS)$. If $u=vt$ is an actual prefix,
then $R(u)=\partial_tR(v)$. All residuals and derivatives refer to this
same $C$. The forward ingredient is the usual right-language description
of a finite prefix automaton, as in Daciuk, Mihov, Watson and Watson,
[*Incremental construction of minimal acyclic finite state automata*,
§§2–3](https://aclanthology.org/J00-1002.pdf). Its use here does not add
the deletion actions defined below.

**Definition 1.2 (public type, inputs and responses).** The public type is
$(k,d)$ with $0\le d\le k\le n$. The full state carrier at this type is
$P_k$; $d$ is the remaining total deletion credit. The common input names
are $+a$ and $-a$ for every $a\in A$, with precisely these partial actions:

$$
\begin{aligned}
+a:(k,d,u)&\longmapsto(k+1,d,ua),
&&k<n\ \text{and}\ ua\in P_{k+1},\\
-a:(k,d,va)&\longmapsto(k-1,d-1,v),
&&d>0.
\end{aligned}
$$

The root output is only $(k,d)$. A successful action returns its supplied
name and the new public type. A false guard is a missing edge. There is
no failure output, enabled-action query, hidden-next-symbol read, credit
replenishment or archive query. The current word is an extendable
controlled prefix; no immutable full codeword tag is carried. After a
deletion a different supplied value can be appended if the new prefix
is extendable in this same relation.

Let $\mathcal L(k,d,u)$ be the set of all finite words $w$ of common
action names for which every requested edge exists. The
mathematical partial response is the sequence of successful labels and
public types when $w$ is legal, and is undefined otherwise. This partial
response is a semantic comparison, not an additional executable read.
At a fixed initial type the successive public types and successful
labels are forced by $w$, so equality of partial responses is exactly
equality of $\mathcal L(k,d,u)$. States of different types are not
identified.

This is the supplied-prefix contract of
[Bounded Suffix Deletion Boundary, Definitions 1.1–1.3](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDED_SUFFIX_DELETION_BOUNDARY.md),
with an arbitrary finite relation in place of a linear kernel and with
only type as root output. That volume's Theorem 2.2 establishes its linear
equivalence already from legal words alone.

**Definition 1.3 (exact representation and charged width).** A family of
maps $a_{k,d}:P_k\to X_{k,d}$ is exact if on its actual images it determines
every action's strict domain, successful label, public type and successor
$a$-value. The general descent and behavioral-quotient mechanism is
[Process Geometry, Theorems 3.2–3.3 and 6.2](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
Only actual images are counted. An exact conditional width is the number
of required internal labels at one given public type, or its fixed-length
binary encoding size $\lceil\log_2 N\rceil$. Public type is supplied
separately for this width. Counting all public types instead requires
their disjoint union.

These counts specify finite state capacity. They assign no price to the
description of $C$, a transition table, intermediate computation,
initialization, a physical memory device or a retained past archive.
Any additional accessible source record must be included in the declared
joint representation before a claim about that representation's width
is made.

## 2. The bounded-deletion boundary on its actual image

**Definition 2.1 (moving anchor and exact image).** At a type $(k,d)$
uniquely write $u=vt$ with $|v|=k-d$ and $|t|=d$. Define

$$
B_{k,d}(u)=(R(v),t),\qquad Q_{k,d}=B_{k,d}(P_k),\qquad N_{k,d}=|Q_{k,d}|.
$$

The anchor is the earliest prefix reachable by spending all currently
remaining credit. It advances on append and stays fixed on delete. Its
actual image is

$$
Q_{k,d}
=\{(S,t):S\in\mathcal R_{k-d},\ t\in A^d,\
                  \partial_tS\ne\varnothing\},
\qquad
N_{k,d}=\sum_{S\in\mathcal R_{k-d}}|\operatorname{Pref}_d(S)|.
\tag{2.1}
$$

For the image identity, choose $v$ representing $S$. The condition
$\partial_tS\ne\varnothing$ is exactly $vt\in P_k$, so every displayed
pair is realized. Conversely every actual prefix satisfies that
condition. Thus (2.1) does not replace a joint image by a free product.

**Theorem 2.2 (strict anchored specialization).** For every admissible
type and $u,u'\in P_k$,

$$
\mathcal L(k,d,u)=\mathcal L(k,d,u')
\quad\Longleftrightarrow\quad
B_{k,d}(u)=B_{k,d}(u').
\tag{2.2}
$$

On the actual images the append guard is
$k<n$ and $\partial_{ta}S\ne\varnothing$. Its boundary update is

$$
\begin{aligned}
(S,\epsilon)&\xrightarrow{+a}(\partial_aS,\epsilon),&&d=0,\\
(S,cw)&\xrightarrow{+a}(\partial_cS,wa),&&d>0,
\end{aligned}
\tag{2.3}
$$

where $c$ is the first symbol of the current tail. The delete guard is
$d>0$ and $t=wa$, and its update is

$$
(S,wa)\xrightarrow{-a}(S,w).
\tag{2.4}
$$

The target types are respectively $(k+1,d)$ and $(k-1,d-1)$.
Consequently $Q_{k,d}$ is the exact behavioral boundary for this contract.
Every exact representation's actual image maps uniquely onto $Q_{k,d}$
by sending $a_{k,d}(u)$ to $B_{k,d}(u)$, and $N_{k,d}$ is its least
conditional width.

Proof. For append, $vta$ has a completion exactly when
$\partial_{ta}S\ne\varnothing$. When $d>0$, the new anchor is $vc$ and
the new $d$-tail is $wa$; $R(vc)=\partial_cS$. When $d=0$ the new
anchor is the entire $ua$. For delete the shorter prefix is extendable
because a completion of $va$ supplies a completion beginning with $a$
for $v$. Its anchor length stays fixed, since
$(k-1)-(d-1)=k-d$. These formulas preserve each guard, missing edge,
label and successor on the actual images. Induction on action-word
length gives the forward implication from boundary equality to response
equality, including arbitrary legal interleavings.

For the converse, unequal tails can be separated by deleting symbols
of one tail in reverse order until the first disagreement from the
right. This uses at most $d$ credits; the first state has every requested
edge and the other misses the disagreeing delete edge. If the tails
agree but the anchor residuals differ, choose a full completion
$f\in S\mathbin{\triangle}S'$. Delete the common tail, spending exactly
$d$ credits, and then supply the symbols of $f$ in order. The whole
word is legal exactly on the side containing $f$: its endpoint has
length $n$, where extendability is membership in $C$. Every intermediate
prefix on that side is extendable.

These explicit separators identify the behavioral fibers for this
particular action contract. The stated factor and minimum then apply
Process Geometry's cited strict quotient property; they are not a
separate general automata-minimality principle. In particular, strict
descent from equal $a$-values forces equal responses and hence equal
$B$-values, making the onto map well-defined. Its uniqueness follows
from surjectivity onto the actual $a$-image. $\square$

**Proposition 2.3 (horizon and endpoints).** Every legal step decreases

$$
V(k,d)=n-k+2d
$$

by exactly one. The longest legal action word from every state has
length $V(k,d)$, and the separators in Theorem 2.2 have length at most
this number. The endpoint counts are

$$
\begin{aligned}
N_{k,0}&=|\mathcal R_k|, &
N_{k,k}&=|P_k|,\\
N_{n,d}&=\sum_{S\in\mathcal R_{n-d}}|S|, &
N_{n,0}&=1,\qquad N_{n,n}=|C|.
\end{aligned}
\tag{2.5}
$$

For $n=0$ the only type is $(0,0)$ and the only boundary point is
$(\{\epsilon\},\epsilon)$.

Proof. Substitute each type update into $V$. Its nonnegativity bounds
all paths. Delete the whole current tail and append any completion
of the anchor to attain $d+(n-k+d)=V$. Tail separators use at most $d$
steps and residual separators at most $d+(n-k+d)$. For $d=0$ there is
only the empty tail. For $d=k$, $S=C$ is fixed and the tail is exactly
the whole prefix. At $k=n$, the allowed $d$-tails for $S$ are its full
words, so $\operatorname{Pref}_d(S)=S$. Finally nonempty $C\subseteq A^0$
forces $C=\{\epsilon\}$. These are the nonlinear endpoint applications
of the same bounded contract as the linear volume's Theorems 2.3 and
3.2. $\square$

**Proposition 2.4 (initialized images and startup).** If an initialized
execution family supplies only $E_{k,d}\subseteq P_k$ at a type, while
all continuations of each supplied state keep the actions of Definition
1.2, its least conditional width is $|B_{k,d}(E_{k,d})|$. For a nonempty
such family the full count applies exactly when this image is all
$Q_{k,d}$. A singleton known initial state at type $(k_0,d_0)$ has only
that state reachable again at its initial type. An empty-prefix
initialization in the stated type range has $d=0$ forever.

Proof. The sufficiency and pairwise separators of Theorem 2.2 apply to
any subset of initial states. A return to $(k_0,d_0)$ cannot use delete,
since credit never increases. Without delete, append strictly increases
the cut, so only the empty path returns. At cut zero the condition
$d\le k$ forces zero credit, and neither action can increase it.
This restricts actual images rather than the continuation semantics,
as in the linear volume's Theorem 3.3. Allowing positive credit at an
empty cut would require a different type contract; no such extension
is used here. $\square$

## 3. Differentiation loses predecessor relations

**Definition 3.1 (actual predecessor ambiguity).** Write $E=R(u)$ for
the current forward residual. At a fixed type define

$$
\begin{aligned}
\phi_{k,d}:Q_{k,d}&\to\mathcal R_k\times A^d,
&\phi_{k,d}(S,t)&=(\partial_tS,t),\\
\psi_{k,d}:Q_{k,d}&\to\mathcal R_k,
&\psi_{k,d}(S,t)&=\partial_tS,\\
\mathcal P_{k,d}(E,t)
&=\{S\in\mathcal R_{k-d}:\partial_tS=E\},
&h_{k,d}(E,t)&=|\mathcal P_{k,d}(E,t)|.
\end{aligned}
$$

Since $E\in\mathcal R_k$ is nonempty, every $S$ counted in this fiber
gives an actual pair $(S,t)\in Q_{k,d}$. Set $h(E,t)=0$ for pairs not
realized, and omit the subscripts when the type is fixed. This relation
identifies which earlier completion sets could have produced the
current completion set along the retained suffix. The suffix specifies
the derivative taken; it need not specify its preimage.

**Proposition 3.2 (conditional recovery and supplier application).**
At a fixed type the earlier residual is recoverable from $(E,t)$ for
every actual prefix exactly when every realized $h(E,t)$ equals one,
equivalently when $\partial_t$ is injective on

$$
\{S\in\mathcal R_{k-d}:\partial_tS\ne\varnothing\}
$$

for each attainable $t$. Given $(E,t)$, the least supplemental alphabet
recovering the entire anchored boundary has size

$$
H_{\rm tail}(k,d)=
\max_{(E,t)\in\phi_{k,d}(Q_{k,d})}h(E,t).
\tag{3.1}
$$

Given only $E$, its least supplemental alphabet has size

$$
H_{\rm forward}(k,d)=
\max_{E\in\mathcal R_k}\sum_{t\in A^d}h(E,t).
\tag{3.2}
$$

In particular

$$
N_{k,d}=\sum_{E\in\mathcal R_k}\sum_{t\in A^d}h(E,t).
\tag{3.3}
$$

A fixed-length binary supplement requires respectively
$\lceil\log_2H_{\rm tail}\rceil$ or
$\lceil\log_2H_{\rm forward}\rceil$ bits. These supplements restore
behavioral boundary points, not necessarily literal prefixes.

Proof. The actual fiber of $\phi$ above $(E,t)$ is in bijection with
$\mathcal P(E,t)$ by $S\mapsto(S,t)$. The fiber of $\psi$ above $E$ is
the disjoint union of these fibers over $t$. This proves their exact
sizes and (3.3); the fibers need not be uniform.

Apply
[ExactRollbackInjectivityCriterion](../../../D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.lean),
declaration `exact_rollback_iff_joint_record_injective`, with nonempty
$X=Q_{k,d}$, $U=\phi$ and a constant extra record. An inverse for $\phi$
is exactly recovery of $(S,t)$; since $t$ is already known it is
equivalent to recovery of $S$. The supplier's injectivity condition
is precisely the singleton-fiber condition above.

Apply
[MinimumRollbackAlphabet](../../../D5/S0/History/Coding/MinimumRollbackAlphabet.lean),
declaration `minimum_rollback_alphabet`, with finite $X=Q_{k,d}$ and $U=\phi$,
then with $U=\psi$. Take the respective finite actual target images
as its enumerated $Y$. Their largest fibers are (3.1) and (3.2), so
the supplier gives both the lower bounds and attaining fiberwise
labels. Labels on prefixes are obtained by pulling them back along
$B$. Conversely one prefix representative per boundary point yields
the same lower bound for any prefix-dependent labeling. All source
and target images here are finite and nonempty.

This applies the existing inverse and coding results to the displayed
predecessor relation; it supplies no additional general inverse or
minimal-alphabet theorem. Label existence also supplies no channel
by which an observer has acquired the label. $\square$

**Proposition 3.3 (exact refinement incidence).** For $0\le d\le e\le k$,
the same actual prefixes induce an onto comparison map

$$
\rho_{e,d}:Q_{k,e}\to Q_{k,d},\qquad
(S,wt)\longmapsto(\partial_wS,t),\qquad |w|=e-d,\ |t|=d.
\tag{3.4}
$$

For $d<k$, a fiber of $\rho_{d+1,d}$ above $(T,t)\in Q_{k,d}$ has
exactly

$$
I_{k,d}(T)=
\sum_{a\in A}
|\{S\in\mathcal R_{k-d-1}:\partial_aS=T\}|
\tag{3.5}
$$

points. Thus the least supplement for this refinement is the maximum
of (3.5) over attained targets; recovery without a supplement holds
exactly when all these fibers have size one. These are comparisons of
two resource contracts on the same prefixes, not executable grants
of deletion permission.

Proof. Decomposing one actual prefix at both anchors gives (3.4) and
surjectivity. For one step, its fine boundary is $(S,at)$ with
$\partial_aS=T$. Conversely any representative $v$ of such an $S$
has $vat\in P_k$, since
$\partial_{at}S=\partial_tT\ne\varnothing$. Hence every predecessor
pair $(S,a)$ is realized; different pairs give different fine
boundary points, and no extra points are counted. The last assertions
apply the suppliers of Proposition 3.2 to this actual map.
$\square$

**Proposition 3.4 (the cancellative comparison with the linear source).**
If the residuals at each cut are pairwise equal or disjoint, every
nonempty fixed-suffix derivative is injective on the actual residual
family. Each adjacent refinement fiber in (3.5) then has size between
one and $q$, and

$$
1\le \frac{N_{k,d+1}}{N_{k,d}}\le q.
\tag{3.6}
$$

This premise holds for $C=\ker H$ over $\mathbb F_q$. The exact linear
factors $1$ or $q$ additionally use the linear uniform-fiber structure
of
[Bounded Suffix Deletion Boundary, Theorems 4.2–4.3](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDED_SUFFIX_DELETION_BOUNDARY.md).
Equal-or-disjoint residuals alone do not force that dichotomy.

Proof. If $\partial_tS=\partial_tS'\ne\varnothing$, an element $f$
in their common derivative gives $tf\in S\cap S'$. The premise forces
$S=S'$. In (3.5) each letter therefore contributes at most one
predecessor, while surjectivity gives at least one predecessor in total.
Summing fibers gives (3.6).

For a linear kernel, at one cut residuals are nonempty solution sets
of the same completion map, with right-hand side the negative prefix
syndrome. Different right-hand sides give disjoint fibers. Given
current syndrome $s$ and tail $t$, the earlier syndrome is
$s-H_Dt$ in the notation of the linear volume. This is exactly its
conditional cancellation step. The structured forward state-space
ingredient is Forney's
[*Codes on Graphs: Fundamentals*, §§5.5 and 6.3](https://arxiv.org/html/1306.6264v2):
its linear/group hypotheses and, for cycle-free minimality, connected
normal realization with internal trimness and properness are retained.
They do not impose uniform fibers on arbitrary nonlinear $C$.

For failure of the dichotomy without linearity, take
$C=\{000,011,101\}$. Its cut-one residuals are
$\{00,11\}$ and $\{01\}$; its cut-two residuals are
$\{0\}$ and $\{1\}$. At every cut distinct residuals are disjoint.
Nevertheless (2.1) gives $N_{3,1}=2$ and $N_{3,2}=3$, so this adjacent
ratio is $3/2$.

Symbolwise injectivity of a partial automaton is established
reversibility terminology; see Radionova and Okhotin,
[*A hierarchy of reversible finite automata*, Definition 2](https://arxiv.org/html/2411.14538v1).
Here it is used on the actual layered forward residual quotient.
Existence of some larger reversible recognizing automaton does not
make that quotient injective: every finite code has a reversible
prefix trie, since each nonroot trie vertex has only one parent.
The retained-input notion in Lavado, Pighizzini and Prigioniero,
[*Weakly and Strongly Irreversible Regular Languages*, Definition 1](https://arxiv.org/pdf/1708.06465),
likewise concerns reconstructing the immediate predecessor from recent
inputs; its input length parameter is not a nonreplenishing deletion
credit. These are attributed intermediate concepts in this comparison,
not new reversibility claims. $\square$

**Proposition 3.5 (fixed-type compression need not stay closed).** Exact
recovery from current residual and tail at one type does not guarantee
that this compressed record is exact at every successor type.

Proof. Let $C=\{000,001,100\}$ and consider $(k,d)=(2,1)$.
The actual prefixes are $00,10$. Their anchor residuals are
$\{00,01\}$ and $\{00\}$ and their common tail is $0$.
The current residuals are respectively $\{0,1\}$ and $\{0\}$, so
$(E,t)$ determines the anchored boundary at this type.
Both can append $0$. At type $(3,1)$ the resulting prefixes $000,100$
have the same current residual $\{\epsilon\}$ and tail $0$,
but $-0,+1$ is legal only from $000$.
Thus a record used throughout a run must satisfy the recovery condition
on every relevant type, or retain a sufficient label there.
$\square$

## 4. Sharp one-recut cost at prescribed forward width

**Theorem 4.1 (sharp binary local bound).** Let $A=\{0,1\}$ and
$1\le k\le n$, and prescribe forward width $N=|\mathcal R_k|$.
Every $E\in\mathcal R_k$ satisfies

$$
|\psi_{k,1}^{-1}(E)|\le2(N+1),\qquad
N_{k,1}\le2N(N+1).
\tag{4.1}
$$

With the last bit also given, every realized $h(E,b)\le N+1$.
If both append values are legal at every prefix in $P_{k-1}$, these
three upper bounds improve to $2N$, $2N^2$ and $N$, respectively.
For every integer $N\ge1$ there is a fixed-length binary relation
attaining all three unrestricted bounds, and another attaining all
three full-branching bounds.

Proof. Every earlier residual is determined by its derivative pair:

$$
S=0\,\partial_0S\ \mathbin{\dot\cup}\ 1\,\partial_1S.
\tag{4.2}
$$

Each component is either empty or a member of $\mathcal R_k$.
Fixing $\partial_bS=E$ leaves at most $N+1$ choices for the other
component. Sum over two bits for a fiber of $\psi$, and then over
the $N$ current residuals for the total. Under the full-branching
hypothesis neither component is empty, so there are only $N$ choices.

For sharpness choose $N$ distinct binary words $f_1,\ldots,f_N$ of
one length $r$. Put $T_0=\varnothing$ and $T_i=\{f_i\}$ for $i>0$.
Choose distinct anchors $v_{ij}$ of one length $\ell$ for all
$(i,j)\in\{0,\ldots,N\}^2\setminus\{(0,0)\}$, taking
$2^\ell\ge(N+1)^2-1$ and $2^r\ge N$. Define the one actual relation

$$
C_N=
\{v_{ij}0f_i:i>0\}\ \cup\
\{v_{ij}1f_j:j>0\},
\tag{4.3}
$$

where the pairs range over that anchor set. At cut $k=\ell+1$ its
current residuals are exactly $T_1,\ldots,T_N$, while the earlier
residuals are exactly all nonzero pairs $0T_i\cup1T_j$.
For a fixed $T_s$ and fixed last bit there are $N+1$ such predecessors;
for $T_s$ without the bit there are $2(N+1)$ fine points.
Thus the total is $2N(N+1)$. Restrict the anchor index set to
$\{1,\ldots,N\}^2$. Then both branches are present and the same
calculation gives $N$, $2N$ and $2N^2$.

Every tuple in these counts has an explicit source prefix in (4.3).
Theorem 2.2 supplies its bounded-deletion separators. Sharpness is
therefore about actual behavioral images, rather than formal derivative
tuples without representatives. Lengths may vary with $N$; no claim
of attainment at every prescribed pair of lengths is made.
The counting deduction concerns this operation contract and does not
assert literature priority over general reversible-automaton or
trellis results. $\square$

**Definition 4.2 (fixed-binary selector relation).** For $m\ge1$ put
$M=2^m$, $n=3m+1$, and

$$
C_m=\{ij0i:i,j\in\{0,1\}^m\}
       \ \cup\
       \{ij1j:i,j\in\{0,1\}^m\}.
\tag{4.4}
$$

There are exactly $2M^2$ codewords. The alphabet of values stays binary
and the common action alphabet stays $\{+0,+1,-0,-1\}$ as $m$ varies.
The selector cut is $k_*=2m+1$.

**Theorem 4.3 (exact selector fibers and lawful separators).** For this
same $C_m$,

$$
N_{k_*,0}=M,\qquad N_{k_*,1}=2M^2,\qquad
\frac{N_{k_*,1}}{N_{k_*,0}}=2M.
\tag{4.5}
$$

Each current-residual fiber has exactly $2M$ one-credit boundary
points. With the selector bit also given, each fiber has exactly
$M$ points. Hence the exact supplements are $2M$ and $M$ labels,
respectively $m+1$ and $m$ fixed-length binary bits. The family attains
the full-branching bound of Theorem 4.1 with $N=M$.

Proof. At the preceding cut,

$$
S_{ij}=R(ij)=\{0i,1j\},\qquad
\partial_0S_{ij}=\{i\},\qquad
\partial_1S_{ij}=\{j\}.
\tag{4.6}
$$

The $M^2$ residuals $S_{ij}$ are distinct: their two first-symbol
branches recover $i$ and $j$. Every $ijb$ is extendable.
The forward residuals at $k_*$ are all $M$ singleton languages
$\{x\}$, whereas the one-credit boundary is $(S_{ij},b)$, yielding
$2M^2$ points.

If two selector bits differ, the requested delete of one is legal
on only one side. With equal bits and different $i$-components,
use $-b,+0$ followed by the $m$ supplied bits of the first $i$.
With equal bits and different $j$-components, use $-b,+1$ followed
by the first $j$. Each experiment uses one delete and $m+1$ appends,
within the exact horizon $m+2$; it is legal on exactly one side.
Deleting the selector and supplying a new one changes the controlled
prefix through the declared actions of this same $C_m$.
It does not replace a hidden tagged codeword.

Above $\{x\}$ the fine points are the disjoint families

$$
\{(S_{xj},0):j\in\{0,1\}^m\}
\quad\text{and}\quad
\{(S_{ix},1):i\in\{0,1\}^m\}.
\tag{4.7}
$$

Thus every forward fiber has $2M$ points, and every fixed-bit fiber
has $M$. Proposition 3.2 supplies the optimal alphabet conclusion.
An explicit attaining label is

$$
L(ij0)=(0,j),\qquad L(ij1)=(1,i);
\tag{4.8}
$$

if $b$ is separately supplied, retain only the unused component.
The current residual gives the selected component and (4.8) gives
the rest, so the anchored boundary is recovered.

For a known bit $0$, all $S_{xj}$ differentiate to $\{x\}$ as $j$
varies. This is the precise missing predecessor relation. It disproves
an alphabet-only factor-two bound at the same cut for arbitrary
nonlinear relations. The unbounded claim varies $m$ and the relation:
every individual $C_m$ is finite. $\square$

## 5. Local amplification and peak width are different counts

**Theorem 5.1 (universal full-carrier peak comparison).** Put
$r_k=|\mathcal R_k|$. For every type,

$$
N_{k,d}\le q^d r_{k-d}.
\tag{5.1}
$$

For a prescribed maximal credit $0\le D\le n$, define the full-carrier
conditional peaks

$$
K_0=\max_{0\le k\le n}r_k,\qquad
K_D=\max_{\substack{0\le k\le n\\0\le d\le\min(D,k)}}N_{k,d}.
$$

Then

$$
K_0\le K_D\le q^D K_0.
\tag{5.2}
$$

If types are counted as part of a single disjoint state alphabet, put

$$
T_0=\sum_{k=0}^n r_k,\qquad
T_D=\sum_{d=0}^D\sum_{k=d}^nN_{k,d}.
$$

The corresponding comparison is

$$
T_0\le T_D\le\left(\sum_{d=0}^Dq^d\right)T_0.
\tag{5.3}
$$

Thus a binary one-credit design has conditional peak factor at most
two and total typed factor at most three. For $n=0$, both available
counts are one and there is no positive-credit type.

Proof. The actual image in (2.1) is a subset of
$\mathcal R_{k-d}\times A^d$, giving (5.1). Take maxima and use
$d\le D$ for the upper bound in (5.2); the included $d=0$ types give
its lower bound. For the sum, reindex $h=k-d$:

$$
\sum_{k=d}^nN_{k,d}
\le q^d\sum_{h=0}^{n-d}r_h
\le q^dT_0.
$$

Summing proves (5.3). None of these inequalities compares
$N_{k,1}$ to $r_k$ at the same cut. They compare complete full-carrier
profiles, conditional on public type in (5.2) and including that type
in (5.3). Restricted initialized images must instead be counted as in
Proposition 2.4. $\square$

**Theorem 5.2 (exact selector-family profile).** For $C_m$ the full
forward profile is

$$
r_k=
\begin{cases}
2^k,&0\le k\le2m,\\
2^{m-\ell},&k=2m+1+\ell,\quad0\le\ell\le m.
\end{cases}
\tag{5.4}
$$

The full one-credit profile, whose types start at $k=1$, is

$$
N_{k,1}=
\begin{cases}
2^k,&1\le k\le2m,\\
2M^2,&k=2m+1,\\
2^{m-\ell+1},&k=2m+1+\ell,\quad1\le\ell\le m.
\end{cases}
\tag{5.5}
$$

Consequently $K_0=M^2$ and $K_1=2M^2$, attaining (5.2)'s binary
factor-two bound. The difference of conditional peak binary widths
is one bit, from $2m$ to $2m+1$, while the width difference at the
selector cut alone is $m+1$ bits.

Proof. Before the selector every binary prefix is extendable. Distinct
prefixes already specify different bits in $i$ or $j$. Complete the
unfinished pair according to one representative, choose selector $0$
if an $i$-bit differs, or $1$ if the difference is in $j$, and append
the chosen component. That completion is legal from the representative
and not the other prefix. Thus all $2^k$ prefixes have different
forward residuals for $k\le2m$. A one-credit boundary still maps onto
these forward residuals and cannot exceed its carrier $P_k$; its
count is therefore also $2^k$ in that range.

After the selector and $\ell$ copied bits, a forward residual is
the singleton unappended selected suffix, of length $m-\ell$.
Every such suffix is realized, giving the second line of (5.4).
For $\ell\ge1$, the one-credit anchor is already after the selector.
Its residual is a singleton $\{ar\}$, where $a$ is the most recently
appended bit and $r$ is the still unappended selected suffix.
The tail is precisely $a$, so the boundary point is
$(\{ar\},a)$. Every word $ar$ of length $m-\ell+1$ occurs, giving
the last line of (5.5). At the selector Theorem 4.3 supplies the
remaining count.

The maxima and binary widths follow from these exact powers of two.
In particular the forward preparation already distinguishes both
blocks at cut $2m$. The unbounded cut-local supplement in Theorem 4.3
does not create unbounded additional peak capacity over that
preparation. $\square$

## 6. Same-source initialization, retention and safe acquisition

**Definition 6.1 (acquired initialization and exact monitor).** Fix
known $C$, an initial type $(k_0,d_0)$ and a nonempty actual initial family
$E_0\subseteq P_{k_0}$. An initialization record is a map
$I:E_0\to Z$ whose value is actually supplied to the controller.
A deterministic boundary monitor initializes its internal state
as a function of that acquired value and subsequently uses only
successful supplied actions and public types. It must decode the
current $B$-value at initialization and after every legal finite
execution from each initial state. Its task includes all the
original strict action domains, so it may not remove distinguishing
continuations to shrink the task.

This acquired-record requirement is the same-source policy distinction
of
[Process Geometry, Theorems 3.4 and 6.5](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
The complete legal-word semantics of Definition 1.2 is not given to
the monitor as an oracle.

**Proposition 6.2 (initialized maintenance).** In this contract an exact
monitor exists precisely when

$$
I(u)=I(u')\quad\Longrightarrow\quad
B_{k_0,d_0}(u)=B_{k_0,d_0}(u')
\qquad(u,u'\in E_0).
\tag{6.1}
$$

A known initial prefix supplies such an initialization. Once the
boundary is initialized, any injective encoding of its relevant
actual image at each type admits deterministic exact updates. A
common internal alphabet of size the maximum of those image sizes
suffices when the public type is separately available.

Proof. At time zero, equal acquired records yield equal initialized
memory and hence equal decoded boundaries, proving necessity.
Under (6.1), assign to each actual acquired record its unique boundary.
Use (2.3)–(2.4) on each successful supplied action. Induction gives
the correct boundary and its exact next-action domains at every stage.
A known prefix determines its residual and tail from the fixed $C$.

For an encoded boundary, decode using the known current type, apply
the strict update, and encode using the new type. Fiber labels may
be reused between different types because the decoder knows the
type. The finiteness of $C$, the action alphabet and the type range
makes all relevant images finite. This argument consumes the existing
factorization principle with the explicit anchored updates; it does
not assert a new general reconstruction theorem or a bound on the
work, scratch space or transition description needed by an encoding.
It also does not acquire an initial value when (6.1) fails.
$\square$

**Theorem 6.3 (causal selector retention with sharp handoff).** In
$C_m$, initialize at type $(1,1)$ with prefix $a\in\{0,1\}$ whose
value has been supplied and acquired. Observe the succeeding actual
supplied append values. There is an exact same-source monitor for
all legal future interleavings. Along an append-only preparation,
both blocks $i,j$ are acquired before the selector. At that selector,
the record

$$
(x,b,e)=
\begin{cases}
(i,0,j),&b=0,\\
(j,1,i),&b=1
\end{cases}
\tag{6.2}
$$

is the exact one-credit boundary in alternate notation: $x$ is the
forward singleton's word, $b$ is the selector and $e$ is the unused
block. Its supplement $(b,e)$ has $2M$ labels, or $e$ has $M$ labels
if $b$ is already retained. These are the least handoff alphabets
when the receiver is respectively given $\{x\}$ or $(\{x\},b)$.

If the selector is deleted, the record reconstructs $S_{ij}$ at
$(2m,0)$. If instead a copied bit $a$ is appended with credit still
one, the record can discard the unused block and keep the selected
word $x=ar$; the new exact boundary is $(\{ar\},a)$.
Across this initialized family the minimal monitor can attain the
conditional peak width $2M^2$.

Proof. Each supplied first bit is an admissible known prefix, so
Proposition 6.2 initializes the boundary without a hidden read.
Its strict updates maintain it on all legal interleavings.
For an append-only preparation, all first $2m$ bits are supplied
inputs. By (5.4) their residuals distinguish the whole prefix, so
the monitor can retain the pair $(i,j)$ through this stage. At the
selector (6.2) is bijective with $(S_{ij},b)$: $x$ and $e$ recover
the ordered pair using $b$. This gives the label (4.8) by retaining
an acquired component before its selector derivative would erase it.
Theorem 4.3 gives the matching handoff lower bounds.

Deleting spends the sole credit, leaving the earlier residual
$S_{ij}$ as the zero-credit forward boundary. On a direct payload
append, the moving anchor becomes $ijb$, whose residual is $\{x\}$;
its tail is $a$, giving exactly the displayed new boundary.
The selector can no longer be exposed by the remaining one delete,
so the unused block has no further role in this boundary task.
After subsequent payload appends the retained singleton includes
the newest bit and unappended suffix as in (5.5); the newest bit
must not be discarded while its deletion is still permitted.

Allow both acquired first-bit initializations and all extendable
append continuations. Their images at each $(k,1)$ are the full
$P_k$, because any actual prefix can be prepared from its first
symbol without spending credit. The exact images at types with
$d=0$ are bounded by the forward profile. Proposition 6.2 and
Theorem 5.2 therefore give the peak $2M^2$.
A single fixed first-bit initialization restricts these images and
is counted by Proposition 2.4 instead. Starting at $(0,1)$ is
outside the contract; starting at $(0,0)$ cannot manufacture this
credit. The initialization used here specifies an actual known
one-symbol prefix with one initial credit and contains no refill.
$\square$

**Theorem 6.4 (safe echo-only acquisition obstruction).** Fix one initial
type and a nonempty finite set of compatible initial prefixes with the
same acquired record. Consider a deterministic adaptive protocol whose
only subsequent outputs are successful public types and supplied
action labels. Require every requested action to be legal for every
still-compatible realization, and allow stopping as a controller
decision. Every finite transcript, stopping decision and returned
answer is identical across those initial prefixes. Such a protocol
cannot recover any target of the initial prefix that is nonconstant
on this initial family.

For $C_m$, even if initialization supplies $(\{x\},0)$ at the
selector, the compatible prefixes $xj0$ have $M$ different initial
anchor residuals. No protocol of the stated kind can acquire the
missing initial residual.

Proof. Initial records and types agree. If transcripts agree through
one stage, the deterministic protocol either stops identically or
requests the same named action. Safety gives a successful edge in
each compatible realization. Its label is that common supplied
input, and its target type depends only on the common old type
and action. Thus the next transcripts again agree. Induction gives
the assertion at every finite stage, including the terminal answer.
A single answer cannot equal two different target values.

In the selector family the $M$ values $S_{xj}=\{0x,1j\}$ are distinct
but have the same derivative $\{x\}$ and retained bit $0$.
For a concrete safe common prefix of an experiment, execute $-0,+1$.
All states reach $xj1$ with credit zero, and the unknown forward
residual becomes $\{j\}$. Since $j$ ranges over all binary $m$-words,
neither next append value is legal for every candidate. No information
about $j$ has been returned. Appending the known selected block along
the original branch can instead make current boundaries coincide;
that changes the later task and does not recover the initial anchor.

The pairwise separating words of Theorem 4.3 certify unequal legal
domains. They are not uniformly safe identification experiments.
Observing an illegal-request response, a timeout encoding legality,
or an enabled-action query would add an output absent from Definition
1.2. Static optimal labels in Proposition 3.2 and retained labels
in Theorem 6.3 are consequently different acquisition assertions.
$\square$

## 7. Source and observation boundaries for further recovery

**Proposition 7.1 (fixed hidden words have a different selector domain).**
The controlled-selector separating actions do not transfer
unconditionally to reading a fixed hidden codeword.

Proof. In $C_m$ fix the tagged full word $z=ij0i$. Define an alternative
cursor contract that keeps $z$ unchanged: a supplied $+a$ is legal
at cursor $r$ only if $r<n$ and $z_{r+1}=a$, and a supplied $-a$
rewinds one position, spending credit, only if the current symbol is
$a$. At cursor $2m+1$ with one credit, $-0,+1$ is absent because the
rewound next hidden symbol remains $0$. In the controlled-prefix
contract, $-0,+1$ is legal from $ij0$ since $ij1$ is extendable in
the same $C_m$. The two contracts therefore have different domains
for a common action word even with the same initial displayed prefix.
The linear version of this source distinction is
[Bounded Suffix Deletion Boundary, Theorem 6.1](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDED_SUFFIX_DELETION_BOUNDARY.md).
$\square$

**Proposition 7.2 (no-adjacent-ones inclusion preserves the example, not
the whole base interface).** Let
$E(x_1\cdots x_m)=x_1\,0\cdots x_m\,0$ and define

$$
C'_m=
\{E(i)E(j)0\,0E(i):i,j\in\{0,1\}^m\}
\ \cup\
\{E(i)E(j)1\,0E(j):i,j\in\{0,1\}^m\}.
\tag{7.1}
$$

Every word has length $6m+2$ and no adjacent ones. At cut $K=4m+1$,
with the controlled actions of Definition 1.2 for this new relation,
its widths and supplements are again $M,2M^2$ and $2M,M$.
This inclusion does not identify its guards or inverse edges with
the unrestricted no-adjacent-ones base.

Proof. Each encoded block ends in zero, and each possible one is
followed by zero, including the selector. At cut $4m$ the residual is

$$
\{0\,0E(i),1\,0E(j)\}.
$$

Its selector derivatives are $\{0E(i)\}$ and $\{0E(j)\}$.
Injectivity of $E$ and the same literal one-symbol selector deletion
give precisely the distinct pairs and fiber counts of Theorem 4.3;
a separator then supplies the new branch, its forced zero and the
encoded component. No two-symbol block deletion is substituted.

The language theorem
[BinaryZeckendorfLanguage](../../../D5/S0/Automata/BinaryZeckendorfLanguage.lean),
declaration `base_success_iff_noAdjacentOnes`, supplies ambient forward acceptance
of these words, including their padded prefixes. It does not impose
the copy constraints in (7.1). At prefix $E(i)E(j)0$, the next $+1$
is absent in this relation because the following symbol is forced
zero. In the no-adjacent-ones base a one after this terminal zero is
legal. Thus even append domains disagree. The exact transition
projection required by
[TypedPartialDFAO](../../../D5/S0/Automata/TypedPartialDFAO.lean),
field `Machine.type_preserving`, preserves and reflects missing edges;
mere language inclusion supplies neither this equation nor a delete
operation. $\square$

**Definition 7.3 (native source/action bridge obligation).** A transfer
to literal $\alpha,\beta$ tree cuts requires a specified map from
one actual native source family to the word-prefix states, a
correspondence of public types and named actions, and preservation
and reflection of each legal domain, label and successor. To transfer
the full lower counts, the compared native family must realize the
relevant word boundary image, or have an independently identified
equally large separated image. A native acquisition claim additionally
requires an actual initial record decoding the mapped boundary and
updates commuting with that decoding as in Proposition 6.2.

The native result
[NativeSymbolicRecutting](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean),
declaration `symbolic_recut_exact`, concerns ordered FreeMagma sources, prefix-free
address cuts, residual variables below a depth bound, reached subtrees,
filled exteriors and equality partitions. Those objects and operations
are distinct from the controlled word-prefix relation. Neither (7.1)
nor an alphabet identification defines the required bridge.
Recovery of physical spatial or temporal readouts further requires
their explicit same-source relations; the finite width counts do not
provide them.

**Proposition 7.4 (mixed-length completion residuals need a different
observation contract).** With type and legal-action outputs only,
completion residuals need not describe the minimal forward boundary
of a mixed-length finite relation. This prevents an unconditional
extension of Theorem 2.2 using the same $R$.

Proof. Let $C=\{0,00,10\}$ and allow appends exactly when their result
is in $\operatorname{Pref}(C)$. At type $(1,0)$ the prefixes $0,1$
have completion residuals $\{\epsilon,0\}$ and $\{0\}$, respectively.
Yet each has exactly the legal action words $\epsilon,+0$: it has no
delete credit, no $+1$ edge, and its $+0$ successor has no further
append. The successful public types and supplied labels agree.
Membership of the current prefix in $C$ is not an output, so these
different residuals are observationally identical.

For this broader observation contract the forward quantity is instead

$$
F(v)=\{w:vw\in\operatorname{Pref}(C)\},
$$

the actual legal append-continuation language. For the displayed
prefixes both values are $\{\epsilon,0\}$. Prefix closure makes a
supplied append word legal exactly when it belongs to $F(v)$.
Adding terminal-membership output would change the comparison.
The fixed-length hypotheses of Definitions 1.1–1.2 avoid that
extra observation: a legal full completion already tests membership
at length $n$. The nonlinear counts, sharp bounds and initialization
results above use only that fixed-length scope. $\square$

## 追加锚（本行以下为增补区）
