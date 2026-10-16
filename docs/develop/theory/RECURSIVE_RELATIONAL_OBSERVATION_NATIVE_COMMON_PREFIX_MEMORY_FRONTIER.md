# Native common-prefix installed-memory frontier

The common prefixes of carefully chosen actual histories give a global
count of installed states for the prescribed native threshold task.
The count applies at both execution minima simultaneously. It is sharp
for the third-hit and third-miss thresholds. Restriction at an actual
live prefix also gives inequalities on the single installed vector of
coordinate-label multiplicities.

## 1. Original task and counted alphabets

**Definition 1.1 (source, code and consumer).** Retain the original
source and output of [WTF, Definitions 1.1–1.2][WTF]. In particular,

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
\tag{CP.1}
$$

The current complete depth-three row $R_*$ has equality classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,
\quad \{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4,
\tag{CP.2}
$$

with whole-subtree disequality between every two different classes.
The domain is the entire unbounded fiber
$\mathcal U_*=\{u\in\mathcal T:R_P(\rho u)=R_*\}$ for
$P=\{L,R\}^3$. The required whole predecessor row is $R_P(u)$,
including the ordered exterior, reached occurrence holes, equality
partition, every retained disequality and strict-prefix blocking guard.
No bound on tree height, size or interior shape is imposed.
The paid table queries the fixed current register $\rho u$ at its
original-root addresses.

Let $n\ge6$, $3\le k\le n-2$, $r\ge0$, and let
$A=\{s_1<\cdots<s_n\}$ consist of positive integers. Put

$$
w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad c_i=s_i+4,
\qquad C_Q=\sum_{i\in Q}c_i,\qquad W=C_{[n]}.
\tag{CP.3}
$$

Thus individual costs are distinct; disjoint subsets may nevertheless
have equal sums. For a branch image $B$, set
$\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}$.
The prescribed pointwise code remains exactly

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ is in any other zero profile}.
\end{cases}
\tag{CP.4}
$$

Here the eleven profiles and the actual class value $x_a$ are those
of WTF Definition 1.1. On arbitrary branch images, alpha, beta and
absent selected replies all contribute zero.

Preparation must enter the original literal latch
$\widehat e_{\sigma_{A,k}(u)}$. The current register is fixed during
preparation and the original complete-entry reader of
[WTF, Convention 1.3][WTF]. That reader has its separately counted
eight states, at most two fresh queries and six submitted letters.
Both original entries and their complete row outputs are fixed.

**Definition 1.2 (installed-state and execution conventions).** A native
preparer is the stationary finite table of WTF Definition 1.4, correct
on every source of $\mathcal U_*$. Every running state has one fixed
absolute word and four fixed successors. It has one source-independent
running start. Its counted current state is its whole changing
configuration. Every installed running state, both original entry
latches and all $r$ further mandated distinct latches count, including
unreachable states. Every actual visit costs one query and its word
length, including constants, roots, absence and post-certificate repeats.

Write $H_P$ for its total installed count. Define the selected classes
using [WTF, Supplier 2.1][WTF]:

$$
E_i=\{p w_i v:p\in\{LLL,LRL\},\
                    v\in\{\varepsilon,L,R\}\}.
\tag{CP.5}
$$

These classes are disjoint. Let $M_i$ count all installed running
states whose words belong to $E_i$, and set
$M(Q)=\sum_{i\in Q}M_i$, $M=M([n])$.
Different states with the same word are counted separately.
Throughout, the native execution caps are uniform over the full fiber:

$$
q_P(u)\le n+1,\qquad \ell_P(u)\le W+3
\qquad(u\in\mathcal U_*).
\tag{CP.6}
$$

The Boolean comparison is exactly [WTF, Definition 3.1][WTF]. It has
$m$ installed running states, two distinct output terminals, one
input-independent running start, and one fixed coordinate and two
fixed successors per running state. All installed running states count.
Each visit to label $i$ costs one query and $c_i$ letters. Every input
$\theta\in\{0,1\}^n$ must terminate with output
$\mathbf1_{\{|\theta|\ge k\}}$, at uniform simultaneous caps
$t\le n$, $J\le W$. Write $m_i$ for its installed multiplicity of
label $i$ and $m(Q)=\sum_{i\in Q}m_i$.

Both models permit arbitrary variable order, state sharing, repeated
queries and cycles in the union graph. Only actual fixed-input runs
must terminate. There is no extra clock, counter, archive, workspace,
computed-address port or uncounted control coordinate.

**Assumption 1.3 (separate native services).** The binding and update of
the actual register, same-version row acquisition and authentication,
lawful native permission, export, complete access isolation, code-only
handoff, lawful complete entry and stationary truthful service are the
supplied services of [WTF, Assumption 1.5][WTF]. Installed-state
cardinality, retained entry contents, address representation, acquired
term work, workspace, elapsed time and physical memory have their
separate meanings and prices.

## 2. Coherent actual witnesses

**Definition 2.1 (live histories and two witness families).** A cube
history includes every invocation already made. Let $S$ be its exposed
coordinate set, $h$ the number of exposed ones, and $z=|S|-h$.
It is live when

$$
0\le h\le k-1,\qquad 0\le z\le n-k.
\tag{CP.7}
$$

For each such pair, define $Z(h,z)$ by giving the successive selected
queries the reply sequence $0^z1^h$, and define $O(h,z)$ using
$1^h0^z$. Between these selected replies follow any native live
nonselected invocation with its cube reply. After the prescribed
sequence, follow such an invocation if present and stop immediately
before the next selected query. The symbols $Z(h,z)$ and $O(h,z)$
denote histories; write $v_Z(h,z)$ and $v_O(h,z)$ for their ending
installed selected states.

**Lemma 2.2 (existence and common-prefix provenance).** Under
Definitions 1.1–1.2, every witness in Definition 2.1 exists and has
actual finite original-source completions for every assignment of its
unexposed bits. Its selected queries are fresh shortest occurrence-root
queries. All $Z(h,z)$ have initial zero histories on one common
all-zero spine; all $O(h,z)$ have initial one histories on one common
all-one spine. In particular:

1. If $z\ge w$, the first $w$ zero exposures of $Z(h,z)$ and
   $Z(g,w)$ query the same coordinates with the same replies.
2. If $g\ge h$, the first $h$ one exposures of $O(h,z)$ and
   $O(g,w)$ query the same coordinates with the same replies.

Proof. The actual simultaneous cube and classification of every finite
address are [WTF, Supplier 2.1][WTF], from [PCA, Lemma 24.1][PCA].
The live-prefix facts used here are [PCA, Theorem 34.3][PCA], as
collected in WTF Convention 6.1: a live selected query is fresh and
has word $LLLw_i$ or $LRLw_i$; the only live nonselected word is
$RLR$, at most once, with its cube-constant beta reply.

Every prefix of either prescribed reply sequence satisfies (CP.7).
Freshness makes its partial assignment consistent, and all of its
Boolean completions are actual cube sources following that history.
A live history cannot latch, since completions require both prescribed
entries. Following the possible $RLR$ call therefore reaches a
selected state. Equivalently, failure to progress would contradict
termination on a cube completion. This also proves that the final
selected state exists when the prescribed sequence is empty or has
length $n-1$.

Determinism, the common start and the fixed cube replies on nonselected
calls make two equal selected reply prefixes literally the same full
native history, including their profile invocations. This proves both
common-prefix assertions. These witnesses give no reply-selection
facility, counter or saved history to the apparatus. $\square$

## 3. Global separation of the witness bands

**Theorem 3.1 (three zero-first hit bands).** All the states

$$
\{v_Z(h,z):0\le h\le2,\ 0\le z\le n-k\}
\tag{CP.8}
$$

are pairwise distinct in the original installed table.

Proof. Reuse the following ordinary supplier statements at the exact
scope (CP.6). [WTF, Theorem 9.1][WTF] says that two live histories
with different hit/zero pairs at the same selected state must admit
the orientation

$$
h<g,\qquad g-h\ge2,\qquad z-w\ge2.
\tag{CP.9}
$$

Furthermore, [PE, Lemma 4.1][PE] excludes properly nested supports,
and [PCA, Theorem 35.1][PCA] excludes equal supports with unequal
hits. For incomparable supports $S,T$ with $h<g$, [PE, Theorem
3.1][PE] gives the implication

$$
\left.
\begin{array}{l}
S\setminus T\text{ is all zero on the }S\text{ history},\\
T\setminus S\text{ is all one on the }T\text{ history}
\end{array}
\right\}
\Longrightarrow
\begin{cases}
|S\setminus T|=|T\setminus S|,\\
C_{S\setminus T}=C_{T\setminus S}.
\end{cases}
\tag{CP.10}
$$

No agreement on the old intersection assignment is required by that
supplier. Both polarity premises in (CP.10) must hold on this one
oriented pair.

Suppose two different witnesses in (CP.8) share a state. By (CP.9)
they must be $Z(0,z)$ and $Z(2,w)$, with $z\ge w+2$. Let $S,T$
be their supports in that order. The support exclusions imply that
they are incomparable. Put $X=S\setminus T$ and $Y=T\setminus S$;
both are nonempty.

The first history is entirely zero, so $X$ is all zero. By Lemma
2.2, the second history's entire initial $w$-zero support is contained
in the first history's longer zero spine. Thus every bit in $Y$ is
one on the second history. Equation (CP.10) applies.

Immediately after the common $w$-zero history, the two histories
query the same next coordinate. The first gives it zero and the
second gives it its first one. That coordinate belongs to $S\cap T$.
The second history has only two ones, so its nonempty private set
$Y$, all of whose bits are one, has size at most one. Equation
(CP.10) consequently makes $X$ and $Y$ disjoint singletons with
equal cost. This contradicts the distinct individual costs in (CP.3).
Every possible collision in (CP.8) has been excluded. $\square$

**Theorem 3.2 (three one-first zero bands).** All the states

$$
\{v_O(h,z):0\le h\le k-1,\ 0\le z\le2\}
\tag{CP.11}
$$

are pairwise distinct in the original installed table.

Proof. Use the same suppliers (CP.9)–(CP.10). A collision of different
pairs in (CP.11) must be between $O(h,2)$ and $O(g,0)$ with
$g\ge h+2$. Their supports $S,T$ must be incomparable. The first
$h$ one exposures are a common history. Every one of the first
history therefore belongs to $S\cap T$, so its private set
$X=S\setminus T$ is all zero. The second history is entirely one,
so $Y=T\setminus S$ is all one. Equation (CP.10) gives equal
private cardinalities and costs. Equal private cardinalities imply
$|S|=|T|$, hence

$$
h+2=g.
\tag{CP.12}
$$

At the first selected query after the common $h$-one history, the
first history supplies zero while the second supplies one. This is
another coordinate in $S\cap T$, distinct from the first $h$
coordinates. Consequently the second history has at least $h+1$
ones in the intersection and only $g=h+2$ ones altogether. Its
nonempty all-one private set $Y$ has at most one element. Again
(CP.10) gives disjoint equal-cost singletons, contradicting (CP.3).
$\square$

**Theorem 3.3 (quantified common-prefix installed-state bound).** For
every $n\ge6$, $3\le k\le n-2$, every original position set $A$
and every $r\ge0$, any preparer correct on all of $\mathcal U_*$
under both caps (CP.6) satisfies

$$
\boxed{\quad M\ge F(n,k):=2n+\max(k,n-k+1)-4.\quad}
\tag{CP.13}
$$

Consequently its total native installed count satisfies

$$
H_P\ge 2n+\max(k,n-k+1)+r.
\tag{CP.14}
$$

Proof. Put $a=k$ and $b=n-k+1$, so $a,b\ge3$ and $a+b=n+1$.
Theorem 3.1 supplies $3b$ distinct states. Add the witnesses

$$
v_Z(h,z),\qquad 3\le h\le a-1,\quad z\in\{b-2,b-1\}.
\tag{CP.15}
$$

There are $2(a-3)$ added witnesses. Any two of them have zero
counts differing by at most one, so cannot collide by (CP.9). In a
collision with an original witness, the lower-hit member would be
the original one. Its zero count is at most $b-1$ and the added
member's zero count is at least $b-2$. This also contradicts (CP.9).
Thus one pairwise separated family in this one table has size

$$
M\ge 3b+2a-6=2n+b-4.
\tag{CP.16}
$$

Theorem 3.2 supplies $3a$ distinct states. Add

$$
v_O(h,z),\qquad 3\le z\le b-1,\quad h\in\{a-2,a-1\}.
\tag{CP.17}
$$

Two added witnesses have hit gap at most one. For a collision
between an added witness and an original witness, (CP.9) requires
the added witness, having the larger zero count, to have the lower
hit count. Its hit count is at least $a-2$, whereas the original
one's hit count is at most $a-1$. The required hit gap of two is
impossible. This gives the second independent bound

$$
M\ge 3a+2b-6=2n+a-4.
\tag{CP.18}
$$

Taking the maximum of (CP.16) and (CP.18), without adding the two
families' sizes, proves (CP.13). Each count is an injection of
explicit actual witnesses into distinct states of one installed table.
There is no summation of repair states or costs from different sources.

[WTF, Lemma 2.2][WTF] supplies two mandatory nonselected running
states outside all $E_i$, in disjoint profile cones, in addition to
the two original entry latches and $r$ further latches. Therefore
$H_P\ge M+4+r$, proving (CP.14). $\square$

## 4. Boolean frontier and exact boundary families

**Definition 4.1 (execution-minimum state counts).** Let
$m_{\mathrm{exec}}(c,k)$ be the minimum installed Boolean running
count among Definition 1.2's graphs at the simultaneous caps $(n,W)$.
Let $H_{\mathrm{exec}}(A,k;r)$ be the minimum total native count at
the simultaneous caps $(n+1,W+3)$. Both minima exist by the grid
construction of [PCA, Theorem 26.1][PCA].

**Corollary 4.2 (unrestricted Boolean count and native offset).** For
the parameters of Definition 1.1,

$$
\begin{gathered}
F(n,k)\le m_{\mathrm{exec}}(c,k)\le k(n-k+1),\\
H_{\mathrm{exec}}(A,k;r)=m_{\mathrm{exec}}(c,k)+4+r.
\end{gathered}
\tag{CP.19}
$$

In particular every unrestricted Boolean competitor at both sharp
caps has at least $F(n,k)$ installed running states.

Proof. [WTF, Theorem 4.1][WTF] is the exact uniform-feasibility
equivalence

$$
\mathsf N_{A,k,r}(H,p,L)
\quad\Longleftrightarrow\quad
\mathsf B_{c,k}(H-4-r,p-1,L-3).
\tag{CP.20}
$$

To apply Theorem 3.3 to an arbitrary Boolean competitor, use its
full-fiber native lift from that theorem. Every Boolean state becomes
one selected occurrence-root state with the same coordinate label;
all installed states, including unused ones, are retained. The lift
adds two profile states, replaces the two Boolean terminals by the
original entry latches, and installs $r$ further latches. It is
correct on the entire original fiber, not just on the cube. Thus its
selected count is precisely the Boolean running count. Theorem 3.3
gives the lower bound. The supplied grid gives the upper bound.
Taking minima in (CP.20) proves the equality in (CP.19).
The offset $4+r$ is relative to the Boolean running count; relative
to the Boolean total $m+2$, it is $2+r$. $\square$

**Corollary 4.3 (exact third-hit and third-miss families).** For every
$n\ge6$, every original $A$ and every $r\ge0$,

$$
\boxed{
\begin{aligned}
m_{\mathrm{exec}}(c,3)
 &=m_{\mathrm{exec}}(c,n-2)=3n-6,\\
H_{\mathrm{exec}}(A,3;r)
 &=H_{\mathrm{exec}}(A,n-2;r)=3n-2+r.
\end{aligned}}
\tag{CP.21}
$$

The existing full-domain grid attains both execution maxima
simultaneously on one actual source and produces the original code
and original complete entry.

Proof. If $a=3$ or $b=3$, the larger of the two separated witness
families in Theorem 3.3 has size $ab=3n-6$. The lower bound equals
the grid upper bound of PCA Theorem 26.1. That theorem supplies one
actual cube source attaining its $n+1$ queries and $W+3$ letters
together; its upper-domain proof covers all eleven original profiles
and arbitrary allowed branch images. Equation (CP.19) gives the native
counts. The five-coordinate third-threshold equality already belongs
to [PCA, Theorem 38.5][PCA] and is not needed here. $\square$

**Corollary 4.4 (size of the remaining grid interval).** Put
$d=\min(k,n-k+1)$ and $e=\max(k,n-k+1)$. The width between the
lower and upper bounds in (CP.19) is

$$
k(n-k+1)-F(n,k)=(d-3)(e-2).
\tag{CP.22}
$$

The improvement in running states over the supplied $2n-2$ bound is
$e-2$. For $n=7,k=4$, (CP.19) reads
$14\le m_{\mathrm{exec}}\le16$ and
$18+r\le H_{\mathrm{exec}}\le20+r$.

Proof. Since $n=d+e-1$, subtracting $2n+e-4$ from $de$ gives
$(d-3)(e-2)$. Subtracting $2n-2$ from $F(n,k)$ gives $e-2$.
The displayed example has $d=e=4$. $\square$

## 5. Actual-prefix inequalities on one installed label vector

**Theorem 5.1 (restriction at an actual live Boolean prefix).** Fix
one Boolean graph of Definition 1.2. For every actual live prefix
with exposed set $S$, assignment $\eta_S$ and $h$ exposed ones,
put

$$
R=[n]\setminus S,\qquad N=|R|,\qquad q=k-h.
\tag{CP.23}
$$

There is a total Boolean threshold graph on $R$, with one
input-independent running start and the same two output terminals,
whose installed running count is at most $m(R)$ and whose uniform
query and letter caps are simultaneously $N$ and $C_R$. If
$N\ge6$ and $3\le q\le N-2$, then

$$
\boxed{\quad m(R)\ge F(N,q)=2N+\max(q,N-q+1)-4.\quad}
\tag{CP.24}
$$

In particular, at residual threshold $q=3$ or $q=N-2$,

$$
m(R)\ge3(N-2).
\tag{CP.25}
$$

These inequalities hold simultaneously for all qualifying actual
prefixes of the same original installed graph.

Proof. Lift the graph to the native full fiber as in Corollary 4.2.
The actual cube prefix in that lift is live, so PCA Theorem 34.3
implies that the original Boolean prefix queried every coordinate in
$S$ once. Its paid costs are exactly $|S|$ and $C_S$. Every
assignment on $R$ extends this prefix, since the graph is
deterministic and all of its previous tests are in $S$. Its remaining
path therefore has at most $n-|S|=N$ queries and $W-C_S=C_R$
letters. Its required output is threshold $q$ on those $N$ bits.

Fix the coordinates of $S$ to $\eta_S$. Retain only $R$-labelled
states occurring after this prefix on at least one completion.
Suppress chains of $S$-labelled states along their now fixed
successors. The initial such chain is finite. A retained edge realized
by some completion also has a finite such chain after it: otherwise
that actual completion would loop. Each chain reaches a retained
state or one of the two original terminals. Since the residual is
live, its initial chain cannot terminate independently of the $R$
input, and hence reaches a retained running start.

If an edge at a retained state is realized by no completion after
the prefix, give it an arbitrary terminal successor. For each fixed
$R$ input, induction follows exactly its original subsequence of
$R$-labelled states. Each outgoing edge in that induction is realized
by this same completion, so no newly assigned impossible edge becomes
reachable. This proves correctness and termination on every $R$
input, even if unrealized union paths in the original graph cycle.

No state has been copied. The installed running count is at most
$m(R)$; suppressing the fixed-coordinate visits can only reduce
both suffix charges on each input. The resulting graph thus has
both caps $N,C_R$. Reindexing $R$ preserves the distinct positive
original positions and costs $c_i=s_i+4$. Apply Corollary 4.2 at
$(N,q)$ to obtain (CP.24), and Corollary 4.3 for (CP.25).

Every application begins with the same multiplicity vector $(m_i)$.
The restricted graphs are proof objects; the original apparatus
receives neither an input restriction nor a free transition.
$\square$

**Corollary 5.2 (native installed-label inequalities).** For one native
preparer satisfying (CP.6), and every actual live cube prefix with
the parameters of (CP.23), if $N\ge6$ and $3\le q\le N-2$, then

$$
M(R)\ge F(N,q).
\tag{CP.26}
$$

In particular $M(R)\ge3(N-2)$ at either residual boundary threshold.
All these inequalities concern the same installed native vector
$(M_i)$, including unused selected states.

Proof. Project this preparer onto the actual cube by the projection
in WTF Theorem 4.1. It retains at most $M_i$ states of label $i$,
suppresses cube-constant chains without unfolding, and preserves the
selected-state subsequence of every actual cube run. Its simultaneous
caps are $n,W$. An actual live native prefix gives the corresponding
Boolean prefix with the same $S,h$. If it ends before a live $RLR$
call, following that fixed cube call first does not change $S,h$.
Apply Theorem 5.1 to the projected multiplicities and use
$m(R)\le M(R)$. The profile call is suppressed only in this proof
projection; it remains paid on each original native run. $\square$

**Proposition 5.3 (a label constraint beyond the total bound).** For
$n=8,k=4$, if $j$ is the label of the Boolean running start, then

$$
\sum_{i\ne j}m_i\ge15.
\tag{CP.27}
$$

Consequently a graph attaining the lower total $m=17$ could have at
most two installed states labelled $j$. The constraint (CP.27) does
not follow just from $m\ge17$, $m_i\ge1$ and at most two
singleton labels.

Proof. Give the initial query answer one. Its actual prefix is live,
has $N=7$ and residual threshold three. Equation (CP.25) proves
(CP.27). Subtracting it from $m=17$ gives $m_j\le2$.

For the nonimplication, take the numerical multiplicity vector with
$m_j=5$, two other entries equal to one and the remaining five
entries equal to two. Its sum is seventeen, all entries are positive,
and exactly two are singletons, but its sum away from $j$ is twelve.
This is an arithmetic counterexample to the implication between
coarse inequalities, not a proposed feasible graph. The singleton
conditions themselves are supplied by [PCA, Lemma 24.2][PCA] through
the full-fiber lift. $\square$

## 6. Hypothesis maps and unresolved frontier

**Definition 6.1 (scope of the counting method).** The witness bands
use actual common-prefix provenance, the live-history separation of
WTF Theorem 9.1, the oriented two-polarity exchange of PE Theorem
3.1, and distinct individual costs. No distinct-subset-sum condition
is assumed. In particular the equal-cost conclusion in (CP.10) is
used only after the chosen histories force both polarity premises.
The counting never asserts that every history at a selected state
has the same support, count pair or residual predicate.

The legal sharing in [PE, Theorem 8.1 and Corollary 8.2][PE], including
its third-threshold specialization, is compatible with these
statements. The separated families here consist only of the specified
zero-first or one-first histories. Theorem 3.3 counts their actual
distinct endpoints and adds only the already disjoint mandatory
overhead. Other live histories and paid post-certificate visits can
share states. No discriminator is assigned to multiple collisions
and then counted repeatedly.

The classical residual-counting reference is Wegener, *The Complexity
of Boolean Functions*, Chapter 14 §4, Definition 4.1 and Theorems
4.1 and 4.3, printed pp. 423–425 [WBP]. His optimal synchronous
construction concerns read-once branching programs. The proof on
printed p. 424 explicitly uses realization of every graph path, a
property it says fails for general branching programs. The grid upper
bound is reused here through PCA Theorem 26.1; that read-once lower
bound supplies no unrestricted inequality in this volume.

Restriction and canonical Boolean representations provide a second
reference frame. Bryant, *Graph-Based Algorithms for Boolean Function
Manipulation*, §1.1 and §2 Definition 1 [BRY], defines restriction as
substitution of a constant and requires strictly increasing coordinate
indices on nonterminal edges. The semantic restriction in Theorem 5.1
is proved directly for the present possibly cyclic union graph. It
imports neither that ordering nor a canonical residual per installed
state. The new counting and installed-label deductions are
repo-derived ordinary mathematics from the explicitly cited suppliers;
no worldwide originality assertion is involved.

**Definition 6.2 (remaining global questions).** For
$\min(k,n-k+1)\ge4$, let

$$
\mathcal G(n,k,c):\qquad
m_{\mathrm{exec}}(c,k)=k(n-k+1).
\tag{CP.28}
$$

Equation (CP.28) remains an open problem here. Equation (CP.22)
gives the remaining numerical interval, not a proof that an intermediate
value is feasible. The actual-prefix inequalities constrain one common
installed label vector, but a packing or whole-table argument attaining
the grid lower bound from them is not established. Extending the
common-prefix separation to middle witnesses must handle their mixed
private polarities; (CP.10) cannot be applied without its two premises.
Alternatively a smaller upper bound requires a complete graph correct
on every Boolean input under both $n$ and $W$, hence a full-fiber
native lift with the prescribed code and entry.

The unrestricted-budget native minimum $H_{\min}$ is a different
quantity. The bounded late-target $F_D/M_1(D)/\lambda$ problem,
dynamic arbitrary-command four-view closure, infinite actual-source
realization and the full space/time/boundary/memory recovery programme
retain their own source, operation, timing and resource obligations.
None is identified with (CP.28) or settled by a finite installed-state
count. Assumption 1.3's separate services and prices remain required.

[WTF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHTED_THRESHOLD_FRONTIER.md
[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[WBP]: https://eccc.weizmann.ac.il/resources/pdf/cobf.pdf
[BRY]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf

## 追加锚（本行以下为增补区）
