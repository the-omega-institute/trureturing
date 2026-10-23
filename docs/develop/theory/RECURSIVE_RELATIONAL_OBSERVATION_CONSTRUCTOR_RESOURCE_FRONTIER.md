# Constructor-elimination fibers and their complete paid resource frontier

This volume supplies the paid-resource interface for the entire family
$\mathcal E_{\rm CE}$ of [ARH, Definition 20.2][ARH]. Its residual
coordinates remain arbitrary nonempty finite ordered trees. The new
logical bridge first quantifies complete sources in the aligned tree
presentation, and then synchronizes the remaining finitely many
observation positions as words. It permits one original-root physical
action to serve charts with different constructor offsets.

The results are ordinary mathematical proofs, not Lean kernel
verification. The source and service interfaces are those of ARH
Assumption 1.3. Acquisition, full accessible-state handoff and certified
epoch are hypotheses; none is provided for free by the decision
procedure. The unrestricted arbitrary signed-fiber problem remains open
at the boundary stated in §9.

## 1. Full sources, actual services and exact inherited charts

**Definition 1.1 (unchanged native contract).** Sources belong to

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho(\alpha)=\beta,\quad
\rho(\beta)=\langle\beta,\alpha\rangle,
\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{CRF.1}
$$

They are complete finite trees, with no uniform size or depth bound.
Let $P,Q$ be the original finite prefix-free cuts, $R$ the acquired
complete old row, $H_0$ the complete retained literal list and
$H_{\rm rel}$ the complete retained signed relation list. Fix

$$
D=\mathcal U_R(H_0,H_{\rm rel})\ne\varnothing.
\tag{CRF.2}
$$

The defining predicates are exactly ARH (1.2)–(1.4): every old repeated
class, every different-class inequality, concrete old exterior,
absent-address guard, literal repetition and signed comparison remains
on the same source. A relation compares entire reached subtrees at its
two recorded epochs. If either endpoint is absent, either sign fails.

Assume this input belongs to $\mathcal E_{\rm CE}$. Its common complete
accessible state and actual original-root register at certified
$N\ge\max(\{0\}\cup\operatorname{epochs}(H_0,H_{\rm rel}))$
satisfy ARH Assumption 1.3. Every remaining source-bearing cache,
address, count, program position, timing field, reference, permission
and archive belongs to that stated input. No unreported source choice
or chart label is available.

A legal service is deterministic and effective, terminates correctly
on each $u\in D$, and returns the entire original $R_Q(u)$: concrete
exterior, reached original holes in their specified order, and their
complete equality partition. It uses actual $\mathsf{Read}(p)$,
forward $\mathsf{ApplyRho}$ on the same register, and absorbing
$\mathsf{Halt}$. Every finite original-root physical word $p$ is legal,
including words with absent replies. Updates disclose no additional
source-dependent information. Local computation depends only on common
input and acquired replies. There is no equality, identity, reset,
reroot, clone, inverse or hidden chart port.

**Definition 1.2 (costs and optimization).** On a source $u$, let

$$
c_A(u)=(q_A(u),a_A(u),\ell_A(u)),\qquad
\ell_A(u)=\sum_{\text{actual Read calls at }p}|p|.
\tag{CRF.3}
$$

Here $q$ counts every actual raw Read call, including repetitions and
absent replies; $a$ counts actual post-entry updates. Halt adds no
read or update. Define the coordinatewise worst vector and the
same-source weighted objective separately:

$$
\begin{aligned}
b(A)&=(\sup_Dq_A,\sup_Da_A,\sup_D\ell_A),\\
\mathcal F&=\{b\in\mathbb N^3:\exists A\text{ legal},\ b(A)\le b\},\\
W_\lambda(A)&=\sup_{u\in D}
 [\lambda_q q_A(u)+\lambda_a a_A(u)+\lambda_\ell\ell_A(u)],
\qquad W_\lambda^*=\inf_A W_\lambda(A),
\quad \lambda\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{CRF.4}
$$

All three summands in $W_\lambda$ concern one run on one source before
the supremum. Installation, computation, address generation, memory,
pre-cut acquisition, authentication, retention, physical time and
energy remain separate. No result below bounds those resources.

**Proposition 1.3 (the exact inherited presentation).** Effectively choose
one accepted cover and one accepted elimination schedule in ARH
Definition 20.2. After discarding exactly empty charts, obtain finitely
many data $(Y_\eta,D_\eta,F_\eta)$ with

$$
\coprod_\eta\{v:Y_\eta\to\mathcal T:D_\eta(v)\}
 \ \xrightarrow[\quad]{(\eta,v)\mapsto F_\eta[v]}\ D
\quad\text{bijectively}.
\tag{CRF.5}
$$

Each $F_\eta$ is a finite normalized constructor template with leaves
$\alpha,\beta$ or $\rho^e(y)$ for fixed $e\in\mathbb N$.
Each $D_\eta$ is a Boolean combination of the aligned atoms
$\rho^i(y)=\rho^j(z)$ and $\rho^i(y)=g$ for finite ground $g$.
Its automaton accepts exactly complete finite satisfying tuples.
A zero-coordinate chart has one ground source or is empty.
The original-prefix recovery decision and its positive determining
prefix and negative finite all-depth witnesses are those of ARH
Theorem 22.1.

Proof. Use ARH Propositions 19.4, 20.3, 20.4, Lemma 21.1 and
Theorem 22.1 at their stated accepted-input scope. The precise local
substitution fact is the following: a selected mandatory equation
$\rho^e(x)=T$, with successful factoring $T=\rho^e(V)$ and
$x\notin V$, is equivalent, by injectivity, to $x=V$.
Restriction of assignments and extension by the unique value $V[v]$
are inverse maps. Substituting in every constraint, source term,
exterior and target term therefore preserves the whole conjunction,
not merely that selected equation. Iterating this identity and the
original chart bijection proves both directions of (CRF.5).
Every surviving variable remains an actual original subtree at its
fixed representative address. No statement about an unaccepted chart
is inferred from Proposition 20.3.

The two original-prefix implications and the bounded prefix chart
selector in Proposition 20.4 are exactly the hypotheses used by
Theorem 22.1. Its negative witnesses fill finite productive assignments
satisfying the entire $D_\eta$. Its positive decision includes a
computable original determining prefix and an actual static service.
These are reused results, including their full-row and access
conditions. $\square$

The new work does not select a source or chart by using this
mathematical presentation. It constructs common physical actions
quantified before all feasible tuples in every chart.

## 2. Finitely many marked positions after quantifying complete trees

**Definition 2.1 (padded word tuples).** Let $\Sigma=\{L,R\}$ and let
$\#$ be a padding symbol. A padded encoding of
$(z_1,\ldots,z_k)\in(\Sigma^*)^k$ is a column word whose $i$th track
is $z_i$ followed by padding. Require a final all-padding column;
additional all-padding columns are permitted. No track resumes after
its first padding symbol. Thus the tuple of empty words is encoded,
and tracks of different lengths are allowed. This is a regular
encoding domain. A relation is word-regular here when the set of all
such encodings of its tuples is a regular finite-word language.

This definition encodes only finitely many address words. It does not
encode an unknown source as a path or truncate a tree at a marked node.

**Lemma 2.2 (finite-marker conversion).** Let
$\varphi(z_1,\ldots,z_k)$ be a WS2S formula on the rooted binary
successor tree with these first-order positions as its only free
variables. It can contain arbitrary quantifiers over positions and
finite sets. One can effectively construct a finite word automaton
accepting exactly the padded encodings of its satisfying tuples.
The case $k=0$ is the decidable truth value of the sentence.
Boolean operations, emptiness and finite word witnesses are effective.

Proof. Replace each free position by a singleton finite-set track,
and conjoin singleton validity. The ordinary WS2S automaton
construction supplies a finite bottom-up tree automaton for these
free tracks after all other variables have been quantified. Use the
finite support-tree convention of MONA §7.2: a support is either
an empty boundary or a labelled node with two support children.
A label is a subset of $\{1,\ldots,k\}$, and track $i$ labels its
unique node $z_i$. An empty boundary carries no marker and denotes
no further support, not an absent node of the infinite address tree.
The relevant interface is acceptance of a finite support encoding,
allowing finite all-zero extensions. Equivalently, the tuple satisfies
$\varphi$ exactly when some such finite support, containing its
marked paths, has an accepting run. The WS2S decision construction
handles projections and finite-support padding before this interface.
This is the standard finite-set interpretation supplied by
[MONA, §§7.1–7.2][MONA].

Here is an explicit conversion of that interface to words. Let $S$ be
the finite state set, including any finite guide-state component.
Compute $Z\subseteq S$, the states attainable by finite all-zero
supports: start from the empty-boundary states and close under
zero-labelled binary transitions. This is a least fixed point on
$S$, so it terminates and every state in $Z$ has a finite zero-support
witness, possibly the empty boundary. Nonproductive states are
excluded.

Read the padded words from their roots toward their ends. At depth
$i$, group the unfinished tracks by their identical length-$i$
prefixes. The groups describe exactly those nodes at depth $i$ that
are ancestors of at least one as-yet-unfinished marked position.
There are at most $k$ groups. Initially all tracks are in the root
group. Store the groups and a guessed state in $S$ for each. Guess
the root state from the accepting states.

For a current group $B$, the next column has the following meaning.
The tracks in $B$ reading $\#$ end at this node; their indices are
exactly its marker label. The tracks reading $L$ form its continuing
left group, and those reading $R$ form its continuing right group.
Guess states for the nonempty continuing groups. A missing group
has no markers anywhere below its child position and may use exactly
a state from $Z$, including a boundary state. Check the binary
transition with those two child states and the specified current
label. Even when all tracks in the group end, the current node is
present with that marker label; only its two children may be empty.
Remove ended tracks, retain the new groups and guessed states, and
advance one column. Permanently ended tracks must continue to read
padding. After all tracks end and all transitions have been checked,
accept and allow any remaining all-padding columns.

Only partitions of subsets of a fixed $k$-element set, track-ending
flags, and at most $k$ states are stored. Thus this is a finite
nondeterministic word automaton. The edge letters determine group
refinement, so distinct prefixes never incorrectly merge. Several
tracks ending at the same node put all their indices on that one
node; a marker that is an ancestor of another is handled by ending
some tracks while the rest continue.

An accepting finite support-tree run restricts to exactly these
states and transitions on the trie of the marked words. Every
off-trie support is finite and zero-labelled, or is an empty
boundary, so its state is in $Z$. This gives an accepting word run.

Conversely an accepting word run prescribes a consistent tree run
on the finite trie of the words. At each missing child attach a
finite zero-support witnessing its chosen state in $Z$. There are
only finitely many attachment sites. The result is a finite support
tree with the required markers and an accepting root. It witnesses
$\varphi$ by the supplied WS2S interface. This proves exactness in
both directions. Finite-state determinization and complement
relative to valid padded tuples give Boolean operations.
Reachable-state search decides emptiness and records a finite word
witness when nonempty. $\square$

The quantifier order in this lemma is substantive. For example, if

$$
\varphi(\mathbf z)=
 \exists X\,[\operatorname{TreeTuple}(X)\land
                  D_\eta(X)\land\operatorname{Tests}(X,\mathbf z)],
\tag{CRF.6}
$$

the complete arbitrary finite trees and their continuations have
already been quantified in WS2S before constructing the marker
automaton. The zero-labelled subtrees in its proof are support
encodings after that quantification. They are not declarations that
the original source ends at a marker. Applying the trie argument
to a source truncated at the markers would not prove (CRF.6).

**Lemma 2.3 (fixed prefixes and shared physical words).** The relations
$p=h z$, for a fixed literal $h\in\Sigma^*$, are word-regular in
$(p,z)$. So are $p=h$, and membership in a fixed finite union of
prefix cones. Finite intersections, unions, complements and
existential removal of word tracks preserve effective word-regularity
in the padded presentation.

Consequently, for finitely many WS2S formulas
$\varphi_j(\mathbf z_j)$ with only their indicated position variables
free, and finitely many constraints
$p_v=h_{jv}z_{jv}$ or fixed-word/cone conditions on $p_v$, it is
decidable whether one tuple $(p_v)_v$ satisfies all the formulas
and word constraints simultaneously. A positive answer supplies
one finite common tuple.

Proof. For $p=h z$, first check the initial $|h|$ symbols of $p$.
While doing so store the symbols arriving on the $z$ track in a
queue. Thereafter compare each $p$ symbol with the appropriately
delayed $z$ symbol. The queue has a fixed maximum length depending
only on $|h|$. Store end flags, require padding in the correct
order, and require that all queued nonpadding symbols have been
matched when $p$ ends. This finite-state test says exactly that
the whole word $p$ is the literal prefix $h$ followed by $z$.
For $h=\varepsilon$ it is the ordinary track equality test.
Fixed words and prefix cones have immediate finite-state tests.

Products, disjoint union and determinization give the stated Boolean
operations, relative to valid padded encodings. For existential
projection, guess the removed tracks column by column. They can
extend beyond the retained words: retain padding on all ended visible
tracks while the guesses finish. Formally the column projection is
a finite alphabet homomorphism and its image is regular; arbitrary
additional all-padding suffixes are allowed in Definition 2.1.
Any extra all-padding columns can also be removed down to the first
complete end column by a finite-state end closure: after all visible
tracks have ended, mark as accepting exactly the states from which
an accepting state is reachable using only all-padding columns.
This is reachability in a finite subgraph. Allow arbitrary additional
all-padding columns and intersect with the valid padded-encoding
domain. This saturates the image over all encodings of the same
visible tuple and implements existential word quantification without
a length bound.

Apply Lemma 2.2 to each formula, lift its automaton to the combined
word tracks, and intersect with all the fixed-prefix tests.
Product-automaton emptiness is a finite calculation. Its finite
accepted tuple proves sufficiency; any satisfying tuple has padded
encodings of a common length and gives a product run, proving
necessity. $\square$

No assertion that fixed left-prefix insertion is WS2S-definable on
two arbitrary tree positions is used. Nor is there an assertion
that every word-regular relation is WS2S-definable. Lemmas 2.2–2.3
give the needed direction and composition with a second, explicitly
proved, word interface.

## 3. Exact chart replies, labels and common actions

**Lemma 3.1 (aligned complete-source formulas).** Each $D_\eta$ has
an effective WS2S formula on complete finite-tree label sets.
For a surviving coordinate $y$, a fixed numeral $e\ge0$, and
an arbitrary position $z$, each reply
$r_{\rho^e(v(y))}(z)$ is expressed by a WS2S formula.
Every fixed original physical-prefix condition on $F_\eta[v]$
therefore has such a formula.

Proof. Encode a coordinate by three finite disjoint label sets
$X_{y,\alpha},X_{y,\beta},X_{y,\mathsf{branch}}$.
Their union contains the root; every other member has a branch parent;
each branch has both children in the union; leaves have neither.
These are exactly complete nonempty finite ordered trees. A separate
triple is used for each coordinate, and all occurrences of a coordinate
use that same triple. Different triples need not be independent or
disjoint from each other.

Encode a run of the supplied ARH Lemma 21.1 automaton for $D_\eta$
by finite state-label sets on the union of these coordinate domains.
Use each coordinate's actual symbol or padding in the transitions,
and require acceptance at the root. This is precisely the aligned
run encoding in SRF Lemma 1.4, with the ARH21.1 residual automaton
in place of the synchronous-family domain automaton. The argument
requires only that this exact residual automaton exists, which
Proposition 1.3 supplies. Zero-coordinate domains use their
computed truth value.

For completeness the variable reply formula uses only fixed right
suffixes. For $c\ne\mathsf{absent}$ it is

$$
\begin{aligned}
\mathsf{Rep}_{e,c}(X_y,z)\quad\Longleftrightarrow\quad&
 [c=\mathsf{branch}\ \land\ z\in X_{y,\mathsf{branch}}]\\
 &\lor
 \bigvee_{\substack{\lambda\in\{\alpha,\beta\}, t\in\operatorname{Pos}(\rho^e\lambda)\\
 r_{\rho^e\lambda}(t)=c}}
 \exists b\,[b\in X_{y,\lambda}\land z=bt].
\end{aligned}
\tag{CRF.7}
$$

Every $t$ in this finite disjunction is a literal word, so $bt$
is a finite composition of successor operations. The absent formula
is the complement of the three nonabsent formulas. Equation (CRF.7)
is SRF (3): the image consists of the preserved original branch
nodes and the finite leaf images rooted at original leaves.
It covers $e=0$, the root, born nodes and absence, and gives exactly
one reply.

For a fixed physical word, navigate the finite $F_\eta$ template.
Either its reply is determined in the ground part, or its remaining
fixed suffix lies in a port $\rho^e(y)$ and uses (CRF.7). This proves
the final claim. All source sets and run sets remain unrestricted
finite sets; the observation depth does not bound them. $\square$

**Proposition 3.2 (whole-row labels from determining cells).** On a positive
ARH22.1 recovery decision one can compute the exact finite image
$\mathscr R=R_Q(D)$ and formulas
$\mathsf{Row}_{\eta,r}(X)$ for $r\in\mathscr R$, partitioning
$D_\eta$ by entire original rows. Equal rows in different charts
receive the same label.

Proof. Use the supplier's original determining prefix, and enlarge
its bound if necessary to an inclusive depth $H$. Enumerate the
finitely many reply vectors $\theta$ on $|p|\le H$ and form

$$
D_\eta(X)\land
 \bigwedge_{|p|\le H}[r_{F_\eta[X]}(p)=\theta(p)].
\tag{CRF.8}
$$

Lemma 3.1 makes every such cell decidable for emptiness in WS2S.
A nonempty cell supplies a finite complete tuple witness; alternatively,
after the positive emptiness decision enumerate finite tuples and
test their concrete predicates until a witness appears. Fill its
template and compute its complete original $Q$ row.

Both source inclusions in (CRF.5) and the determining-prefix property
make this row constant on the entire cell, across charts as well
when the prefix vector agrees. Every source lies in one cell.
Merge equal finite rows by comparing all concrete exterior symbols,
reached positions, canonical numbering and all partition classes.
Disjoin the cells giving each merged row to define
$\mathsf{Row}_{\eta,r}$. Every label is attained by a cell witness,
and every actual source has its correct label.

This is the determining-cell argument of SRF Proposition 1.5 with
the exact suppliers replaced as displayed. Finite image alone is
not its premise. The chart and prefix are construction indices,
not observations given to the running service. $\square$

**Definition 3.3 (finite chart routing at a fixed epoch).** Fix an actual
epoch numeral $n$. Normalize $\rho^n(F_\eta)$, expanding ground
parts completely and leaving each residual occurrence as a port
$\rho^{n+e}(y)$. The finite full constructor template has explicit
internal nodes, ground leaves, and port leaves. Its physical words
are partitioned into finitely many kinds:

- A word exactly equal to an explicit internal-node address or to
  a ground-leaf address; its reply is the known branch or leaf.
- A strict descendant of a ground-leaf address; its reply is absent.
- A word $p=h z$ at a port address $h$ labelled
  $\rho^{n+e}(y)$; its reply is
  $\mathsf{Rep}_{n+e,c}(X_y,z)$.

The first two kinds are fixed-word or finite-cone conditions.
Their replies include all ground births because ground parts were
expanded at $n$. The port addresses are prefix-free within one
template, so the kinds are exhaustive and disjoint. Port copies
use the same coordinate but can have different $h,e$.
No assertion that the partition is the same in different charts
is made.

**Theorem 3.4 (one physical-word relation across all charts).** Fix any
finite list of read indices $v$ with epoch numerals $n_v$. Fix a
finite reply path on some of these indices and, if desired, a
whole-row label $r$. The following predicates in the physical word
tuple $\mathbf p=(p_v)_v$ are effectively word-regular:

1. Some $u\in D$ gives the specified replies.
2. Some such $u$ has whole row different from $r$, on a positive
   recovery instance.
3. No such $u$ exists, or no such wrong-row source exists.

The quantifiers concern complete sources satisfying all constraints.
Word witnesses are common original-root actions, not chartwise
chosen replacements.

Proof. For each chart and each of the finitely many choices of routing
kind at every used index, introduce a suffix word $z_{\eta v}$ only
at port indices. Form in aligned WS2S

$$
\begin{aligned}
E_{\eta,t}(\mathbf z)&=
 \exists X\,[D_\eta(X)\land
                  \mathsf{Path}_{\eta,t}(X;\mathbf z)],\\
B_{\eta,t,r}(\mathbf z)&=
 \exists X\,[D_\eta(X)\land
                  \mathsf{Path}_{\eta,t}(X;\mathbf z)
                  \land\neg\mathsf{Row}_{\eta,r}(X)].
\end{aligned}
\tag{CRF.9}
$$

The path is the conjunction of the prescribed reply formulas;
a wrong known ground reply makes it false. Lemma 3.1 and
Proposition 3.2 justify every component. All coordinate and run
sets are quantified here. The only free variables left are the
finitely many suffix positions.

Apply Lemma 2.2, then impose $p_v=h_{\eta v}z_{\eta v}$ and the
fixed/cone routing conditions by Lemma 2.3. Project away the suffix
tracks. Union over the finite routing choices and charts to obtain
$E_t(\mathbf p)$ and $B_{t,r}(\mathbf p)$. Complement relative to
valid physical-word tuples for item 3. Unused read indices are
unconstrained tracks.

For exactness, every source has its unique chart assignment from
(CRF.5) and every one of its physical words has its unique routing
kind. Its literal replies therefore give the corresponding witness
in (CRF.9). Conversely every witness of (CRF.9), with matching
physical words, fills a complete source in $D$, and (CRF.7) and
the routing identity give precisely its actual replies at those
words and epochs. The wrong-row predicate uses the complete row
classification, so that direction too is exact.

In particular, intersecting several complements $\neg B_{t,r_t}$
over one physical tuple $\mathbf p$ enforces correctness for
every chart on the same installed words. The suffix in each
chart is forced by that word and its selected literal header.
There is no change from
$\exists\mathbf p\ \forall u\in D$
to a chartwise or sourcewise choice of actions. $\square$

**Example 3.5 (unequal constructor headers really occur).** In the
six-hole fiber of §7, at epoch $n$ the physical word beginning
$LL$ reads a suffix in $\rho^n(x)$, while one beginning $RLL$
reads a suffix in $\rho^{n+1}(x)$; the $y$ ports at $LR,RRL$
have exponents $n,n+2$. More generally the reconstruction templates
can copy several coordinates under arbitrary unequal finite headers,
with different headers in different charts. Theorem 3.4 uses
constraints $p=h z$ for these occurrences after complete-source
quantification. It requires neither the common routing tree of
SRF Lemma 1.3 nor recognizability of the direct physical-word/source
convolution excluded by SRF Counterexample 1.6.

## 4. Exact finite budgets and both paid comparator directions

**Definition 4.1 (adaptive finite skeletons).** For integers $k,b\ge0$,
a skeleton is a finite rooted four-reply tree of read depth at most
$k$. Its internal vertices are actual reads; each has one physical
word $p_v$ and one epoch $n_v\in[N,N+b]$, with epochs nondecreasing
along each path. Its leaves are absorbing halts with labels in
$\mathscr R$. A root halt is allowed. At execution, perform exactly
the real updates needed to reach the next read's installed epoch,
submit the installed physical word, and follow its actual reply.
There are no updates after the final read.

For a halt leaf $t$, put

$$
k_t=\#\{v:v\prec t\},\qquad
b_t=n_{\rm last}-N\ \text{or }0\text{ at a root halt},\qquad
L_t(\mathbf p)=\sum_{v\prec t}|p_v|.
\tag{CRF.10}
$$

The relation $E_t$ of Theorem 3.4 says exactly that this leaf is
reachable from some source in the entire $D$. If its installed
label is $r_t$, correctness is exactly

$$
\mathsf{Correct}(\mathbf p)=
       \bigwedge_t\neg B_{t,r_t}(\mathbf p).
\tag{CRF.11}
$$

Shapes, epoch assignments and leaf labels have finite ranges for
fixed $(k,b)$. The words are unbounded. Their lengths in (CRF.10)
are complete original-root lengths, with no header discarded.

**Theorem 4.2 (unbounded-address budget decision).** For every input of
Definition 1.1 and every $k,b\in\mathbb N$, there is a terminating
necessary-and-sufficient decision of

$$
\exists A\text{ legal on all }D:
       \sup_Dq_A\le k\quad\land\quad\sup_Da_A\le b.
\tag{CRF.12}
$$

A positive answer constructs an actual source-total service.
The comparison includes all deterministic effective adaptive serial
services with arbitrary physical words, pointwise finite local work
and absorbing halt.

Proof. Apply the already supplied ARH22.1 recovery decision. If it
is negative, its serial-to-original-prefix implication excludes
every finite raw budget, so (CRF.12) is false. If positive,
compute $\mathscr R$ and its formulas. Enumerate the finitely many
skeleton shapes, epochs and whole-row leaf labels of Definition 4.1.
For each one, Theorem 3.4 constructs a finite word automaton for
(CRF.11). Decide its emptiness. If any is nonempty, extract its
finite tuple of physical words. If all are empty, answer no.
The product-automaton searches terminate; there is no increasing
address cutoff on the negative branch.

For the positive direction, execute an accepted skeleton using only
its installed words and common control. Each actual $u\in D$
has a feasible chart valuation. Induction along the physical
execution and Theorem 3.4 identify its path with that valuation's
actual replies. It reaches a halt in at most $k$ reads and at most
$b$ updates. Equation (CRF.11) forces the leaf label to be its entire
original row. Its actual costs are exactly (CRF.10). No source,
chart or equality query is needed to execute the certificate.

For the converse, fix an arbitrary legal comparator satisfying
(CRF.12). Its common state and the finite reply prefix fix every
subsequent local computation, real update and physical word before
the next reply. At a reachable prefix that segment is finite:
otherwise the comparator would fail to terminate on a source
reaching it. There are at most $1+4+\cdots+4^k$ reachable reply
prefixes. Unroll their finite segments into a finite reply tree,
keeping every actual read, its word, its epoch, and every early
halt. Replace unreachable children by immediate halts. Delete
updates after the final read on any path; they carry no new
source information under the contract and their removal decreases
only the update coordinate. The already determined output can be
returned before those updates.

All remaining read epochs lie in $[N,N+b]$ and are nondecreasing.
Every reachable halt returns some row in $\mathscr R$; label it
accordingly, and choose any row for unreachable halts.
The resulting skeleton is among the finite choices above.
Correctness of the comparator and both source directions in
Theorem 3.4 make (CRF.11) true for its actual words.
Thus a no answer excludes every such comparator.

This last direction is a mathematical unrolling, not an asserted
algorithm extracting a uniform bound from arbitrary source-total
code. The decision constructs its own finite certificate using
the finite automata. $\square$

**Theorem 4.3 (three budgets and exact costs).** For every
$(k,b,L)\in\mathbb N^3$ it is decidable whether that upper-budget
triple belongs to $\mathcal F$. A yes answer constructs a legal
service. For any installed finite skeleton one can compute all
reachable paths, its exact coordinatewise worst vector and every
rational same-source weighted worst value. Each reachable path,
and hence each finite maximum, has an effectively obtainable
complete-source witness in $D$.

Proof. On a positive recovery instance, enumerate the finitely many
skeletons and physical words of length at most $L$. Decide correctness
and each exact leaf reachability using Theorem 3.4, now with fixed
words, and require $L_t\le L$ on every reachable leaf.
This terminates. A passing skeleton executes precisely its path
costs and is sufficient.

Conversely, a comparator meeting the triple has each submitted
word of length at most $L$ on every actual run. Unroll it as in
Theorem 4.2, replacing unreachable children by halts and deleting
trailing updates. Its remaining words are in the finite enumeration,
its total path lengths are unchanged on actual runs, and it passes.
On a negative recovery decision every triple fails by Theorem 4.2.
This proves both directions without claiming a variable-length
arithmetic predicate in WS2S.

For the witness claim, at fixed words choose a chart and routing
alternative making (CRF.9) nonempty for the leaf. The suffixes are
then fixed by the words and headers. The exact WS2S predicate
extracts a complete finite tuple, or a prior yes decision permits
terminating enumeration of concrete satisfying tuples. Equation
(CRF.5) fills an actual original source, and the physical path
identity proves that it attains exactly $(k_t,b_t,L_t)$.
Maximize over the finitely many reachable leaves coordinate by
coordinate, or first sum with the given weights on a leaf and
then maximize. These are different operations. No single source
is asserted to attain several independent coordinate maxima.
$\square$

These constructions retain raw repetitions as actual calls whenever
the installed skeleton repeats one. A later domination argument
can remove redundant calls, but never relabels a simulated event as
an actual receipt. Early epochs zero and one, absent replies,
zero-read services, ground charts, repeated old classes and
off-task inequalities were all included in the predicates above.

## 5. Complete attained Pareto basis

**Proposition 5.1 (the operational suppliers on this same domain).** Put

$$
M_N=\max(N,5),\qquad U_N=M_N-N,\qquad s_N=\max(0,2-N).
\tag{CRF.13}
$$

Every legal comparator on $D$ has a legal sourcewise dominating
replacement with at most $U_N$ actual updates, followed by a
sourcewise dominating cleanup with $q(u)\le\ell(u)+s_N$.
All actual actions through the cap retain their early-epoch options.

Proof. Reuse JRF Theorem 3.1 and Lemma 3.2, also applied to signed
fibers by ABC Proposition 6.4. The underlying transport identity
is JRF Lemma 2.2:

$$
r_{\rho^n u}(p)=r_{\rho^m u}(S(n,m,p)),\qquad
|S(n,m,p)|\le |p|\quad(n\ge m\ge5),
\tag{CRF.14}
$$

for every finite source $u$, with a computable source-independent
word transformation. Restricting its universal source quantifier
to the exact $D$ changes neither side. The common initial state,
one physical register, four replies, source-free update result and
absorbing halt are exactly the interfaces of Definition 1.1.

The supplied simulation keeps actual epoch $\min(n,M_N)$ while
running the comparator's local control. It preserves the raw count,
caps actual updates sourcewise, and decreases each actual submitted
length. Cleanup uses only previously paid same-epoch replies and
the universally known root replies at epochs at least two.
It removes redundant calls, does not add updates, and leaves at
most $s_N$ zero-length information opportunities. The supplier
therefore proves the asserted inequality and sourcewise dominance
on this domain, with pointwise termination. Simulated later events
remain local records rather than actual receipts. No literal-only
source-language decision is used. $\square$

**Definition 5.2 (finite comparison rectangle).** On a positive recovery
decision, take the static service and finite probe bounds supplied
by ARH22.1–22.2. Obtain sufficient budgets $(K_0,0,L_0)$, for
example by multiplying its raw bound by its maximum complete
physical-address length for this $N$. Define

$$
K=\max(K_0,L_0+s_N).
\tag{CRF.15}
$$

These are sufficient bounds, not minimum prices. Neither requires
a uniform bound on unknown residual-tree size.

**Theorem 5.3 (effective complete Pareto basis).** On every positive
recovery instance one can compute a nonempty finite set
$\mathcal B\subseteq\mathbb N^3$ with

$$
\mathcal F=\{b\in\mathbb N^3:\exists v\in\mathcal B, v\le b\},
\qquad \mathcal B=\operatorname{Min}(\mathcal F).
\tag{CRF.16}
$$

For every $v\in\mathcal B$ one can construct a legal finite service
$A_v$ with $b(A_v)=v$ exactly, and actual-source witnesses for its
coordinate maxima. On a negative recovery instance
$\mathcal F=\varnothing$ and every correct service has both
unbounded worst raw count and unbounded worst total address length.

Proof. The finite optimization is JRF Lemma 5.2 and Theorem 5.3
at the following fully matched interfaces: the source domain is
(CRF.2), the static supplier is Definition 5.2, the sourcewise
normalizations are Proposition 5.1, and the two feasibility
decisions and exact witness interface are Theorems 4.2–4.3.
The literal-only logical formulas of JRF are replaced entirely
by Theorem 3.4.

Explicitly, for every $0\le k\le K$ and $0\le b\le U_N$, decide
unbounded-address feasibility by Theorem 4.2. In a true case obtain
a finite skeleton, compute its finite worst length
$L^{\rm wit}_{k,b}$, and find by the finite triple tests the least
feasible $L_{k,b}$ in $[0,L^{\rm wit}_{k,b}]$.
Keep a service for that triple. False cases undergo no address
enumeration. All loops have the displayed finite bounds and all
negative tests are finite-state decisions.

For cofinality, normalize any comparator with finite worst vector,
obtaining worst read and length costs $k',L'$ and updates at most
$U_N$. Cleanup gives $k'\le L'+s_N$.
If $k'\le K$, its pair occurs in the grid and
$L_{k',b'}\le L'$ for its worst update count $b'$.
If $k'>K$, then $k'>K_0$ and $L'>L_0$; the static supplier is
no worse in all three worst coordinates. Its pair is also in
the grid. Thus every feasible upper vector dominates a retained
triple. Conversely every retained triple is feasible by its
constructed service. Take the minimal elements of this finite
set to get (CRF.16). At a minimal element the witness's exact
worst vector cannot be strictly smaller, since that would itself
be a feasible vector. Theorem 4.3 gives the maxima witnesses.

On a negative decision ARH22.1 excludes finite worst read counts.
If some correct service had finite worst length $L$, cleanup
would give a correct read bound $L+s_N$, a contradiction.
This proves the two unbounded coordinates separately. The
cofinality comparison in the positive proof concerns worst
vectors; it does not assert pointwise dominance by one fixed
Pareto service on every source. $\square$

**Corollary 5.4 (infinite upper coordinates and genuine halt).** Allow
upper budgets in $\overline{\mathbb N}^3$, where
$\overline{\mathbb N}=\mathbb N\cup\{\infty\}$.
On a positive instance the feasible extended upper vectors are
exactly those dominating some $v\in\mathcal B$.
On a negative instance they are exactly
$(\infty,b,\infty)$, $b\in\overline{\mathbb N}$, and their
minimal extended vector $(\infty,0,\infty)$ is attained by
a pointwise terminating static service.

Proof. This is JRF Corollary 5.5 with the same matched suppliers.
A finite raw bound gives a finite reachable reply tree and hence
finite maxima of all its installed costs after deleting trailing
updates. A finite length bound first gives a finite raw bound by
cleanup, without increasing any other constrained coordinate.
If both read and length upper bounds are infinite, the static
supplier works on a positive instance.

For every finite source on either branch, a static service can
traverse the entire original tree using the current-epoch historical
literal decoder of SLH Theorem 2.2. Recurse only at a decoded
original branch and stop at each original leaf. Each node costs
finitely many actual current reads; finiteness of the particular
original tree gives termination. Compute its whole row and halt.
This has zero actual updates. On the negative branch Theorem 5.3
forces its two infinite suprema, while every individual run is
finite. No continuation is performed after halt. $\square$

## 6. Same-source weighted minimax, including zero weights

**Theorem 6.1 (effective value and attainment).** For every rational
$\lambda\ge0$, the value $W_\lambda^*$ in (CRF.4) is computable
and attained by a legal actual service.

If $\lambda_q=\lambda_\ell=0$, its value is zero on every
instance. If $\lambda_q+\lambda_\ell>0$ and recovery is
negative, its value is infinity. On every positive recovery
instance the value is a finite rational attained by a finite
skeleton, and an actual source attains its worst weighted cost.

Proof. Apply the reasoning of JRF Theorem 7.1 only after supplying
Theorems 3.4, 4.2 and 4.3. Corollary 5.4's static traversal proves
zero value when only updates are priced, including all weights
zero. On a negative branch Theorem 5.3 forces an infinite weighted
supremum whenever either read or length has positive weight.
The same pointwise total static traversal attains that extended
value; it does not have an infinite run on any finite source.

On a positive branch let

$$
B_0=\lambda_qK_0+\lambda_\ell L_0.
\tag{CRF.17}
$$

The static supplier bounds the optimum by $B_0$.
When $\lambda_q+\lambda_\ell>0$, normalize any comparator
with weighted value at most $B_0$ using Proposition 5.1.
Sourcewise dominance, before taking any supremum, cannot increase
its weighted value. Actual updates are at most $U_N$.
If $\lambda_q>0$, its read bound is
$k_\lambda=\lfloor B_0/\lambda_q\rfloor$.
If $\lambda_q=0<\lambda_\ell$, its length bound is
$L_\lambda=\lfloor B_0/\lambda_\ell\rfloor$ and cleanup
gives read bound $k_\lambda=L_\lambda+s_N$.
These reductions cover comparators with initially unbounded
unpriced coordinates.

For each rational threshold $z\in[0,B_0]$, use the finitely many
skeleton shapes with read depth at most $k_\lambda$ and epochs
in $[N,M_N]$. Require correctness and, on every reachable leaf,

$$
\lambda_q k_t+\lambda_a b_t+
                   \lambda_\ell L_t(\mathbf p)\le z.
\tag{CRF.18}
$$

If $\lambda_\ell>0$, every reached word has length at most
$\lfloor B_0/\lambda_\ell\rfloor$. Enumerate those words,
and test (CRF.18) only at reachable leaves using Theorem 4.3.
Unreachable subtrees may be replaced by halts as in Theorem 4.2,
so this restriction excludes no relevant comparator.

If $\lambda_\ell=0$, then $\lambda_q>0$ and each left-hand
cost is independent of the words. For every numerically violating
leaf require $\neg E_t(\mathbf p)$. Intersect these word-regular
relations with (CRF.11), and decide emptiness with no bound on
physical words. Theorem 3.4 proves exactly the additional
unbounded-address predicate needed on this zero-weight face.
It is not obtained from the finite-length enumeration.

Every original comparator with value at most $z$ has, after the
sourcewise reductions and finite unrolling, a passing certificate
with no larger cost. Conversely, a passing certificate performs
exactly the charged actions on every source and obeys (CRF.18).
These are both paid comparator directions for each threshold.

Choose a positive common denominator $d$ of the weights. Every
finite run sum lies in $d^{-1}\mathbb N$; every bounded nonempty
set of such sums has a maximum on that lattice. Test the finite
list $0,1/d,\ldots,B_0$. The static supplier ensures a true test.
The first true threshold is the exact infimum: a smaller feasible
value would be a smaller true lattice threshold. Extract its
finite service and its worst-source witness by Theorem 4.3.

This minimizes the maximum of the sum on one source. It does not
minimize $\lambda\cdot b(A)$ or choose a source independently
for each summand. The Pareto basis in §5 is not substituted for
these threshold tests. $\square$

## 7. Exact price on the existing six-hole entire fiber

**Definition 7.1 (the unchanged acquired consumer).** Retain precisely
ARH Proposition 23.2:

$$
\begin{gathered}
P=\{LL,LR,R\},\qquad
C=\langle\langle\square_1,\square_2\rangle,\square_3\rangle,
\qquad \pi=\{\{1\},\{2\},\{3\}\},\\
H_0=\{(0,RLR,\alpha),(0,RRR,\beta)\},\\
H_{\rm rel}=
\{(1,LL,0,RLL,=),(2,LR,0,RRL,=),\\
\hspace{32mm}
 (0,LL,2,LR,\ne),(0,LR,1,LL,\ne),(1,LL,2,LR,\ne)\},\\
Q=\{LL,LR,RLL,RLR,RRL,RRR\},\qquad N\ge2.
\end{gathered}
\tag{CRF.19}
$$

The supplied exact fiber, including every guard and old inequality,
is $\{u(x,y):D_6(x,y)\}$, where

$$
\begin{aligned}
u(x,y)&=\left\langle\langle x,y\rangle,
 \left\langle\langle\rho(x),\alpha\rangle,
                   \langle\rho^2(y),\beta\rangle\right\rangle
                                      \right\rangle,\\
D_6(x,y)&\Longleftrightarrow
 x\ne y\ \land\ x\ne\rho^2(y)\ \land\ y\ne\rho(x)
                      \ \land\ \rho(x)\ne\rho^2(y),
\qquad x,y\in\mathcal T.
\end{aligned}
\tag{CRF.20}
$$

Both coordinates remain arbitrary complete finite trees subject
only to $D_6$. This is the entire acquired fiber, not a selected
family. Set $d_N=2+\lceil N/2\rceil$.

**Lemma 7.2 (short probes cannot separate beta from a branch).** For
every finite branch tree $z$, every $j\ge2$, and every word
$s$ with $|s|<\lceil j/2\rceil$,

$$
r_{\rho^j\beta}(s)=r_{\rho^j z}(s)=\mathsf{branch}.
\tag{CRF.21}
$$

Proof. Write $r=|s|$, so $2r\le j-1$.
The supplied all-source branch bound JRF (2.4) says that
$w(t)\le n-2$ implies $r_{\rho^n v}(t)=\mathsf{branch}$
for every finite $v$, where $w(t)=\#_L(t)+2\#_R(t)$.
For $\rho^j\beta=\rho^{j+1}\alpha$ use
$w(s)\le2r\le j-1=(j+1)-2$.

For $z=\langle z_L,z_R\rangle$, the empty suffix sees its
preserved root branch. Otherwise remove its first letter.
The remaining suffix $t$ has weight at most $2(r-1)\le j-3$,
and lies in $\rho^j z_L$ or $\rho^j z_R$.
The same bound with $n=j$ gives branch. It proves existence as
well as the label, so absence cannot distinguish these short
words. $\square$

**Lemma 7.3 (one common hard source with two legal alternatives).** Put

$$
b_1=\langle\alpha,\alpha\rangle,\qquad
b_2=\langle b_1,b_1\rangle,\qquad
u_*=u(b_1,b_2),\quad
u_x=u(\beta,b_2),\quad u_y=u(b_1,\beta).
\tag{CRF.22}
$$

All three sources lie in the same entire fiber (CRF.19).
Their full rows are different. For any legal correct service on
that fiber, the actual run on $u_*$ contains two distinct reads,
each of complete physical length at least $d_N$.

Proof. The supplied clock satisfies
$\kappa(\alpha)=0$, $\kappa(\beta)=1$,
$\kappa\langle s,t\rangle=2+\kappa(t)$ and
$\kappa(\rho t)=\kappa(t)+1$.
For $(b_1,b_2)$ the four clocks of
$x,y,\rho(x),\rho^2(y)$ are $2,4,3,6$;
for $(\beta,b_2)$ they are $1,4,2,6$.
They are pairwise distinct and hence verify $D_6$.
For $(b_1,\beta)$ they are $2,1,3,3$; the only tied comparison is

$$
\rho(b_1)=\langle\beta,\beta\rangle
 \ne\rho^2(\beta)
   =\langle\langle\beta,\alpha\rangle,\beta\rangle.
\tag{CRF.23}
$$

Thus it too satisfies all four inequalities. The two other old
class inequalities and all guards follow from the exact
two-direction supplier (CRF.20); no old condition has been
discarded. All three sources have the fixed six-hole outside
context in ARH (CE.23.11). Their six hole values are
$x,y,\rho(x),\alpha,\rho^2(y),\beta$.
On $u_*$ every class is a singleton; on $u_x$ holes $1,6$
coincide; on $u_y$ holes $2,6$ coincide. In each case the retained
inequalities exclude the other nonconstant comparisons, so
these are different complete rows.

Compare the runs on $u_*$ and $u_x$ until their first differing
literal reply. Such a read must occur before the run on $u_*$
halts. Otherwise common control, all replies and update choices
would remain identical up to that halt, forcing the same output
on sources whose required rows differ. In particular the epoch
at their first differing read is common, say $n=N+a$.

Only the $x$ occurrences can distinguish this pair. Their
original-root cones are $LL\Sigma^*$ and $RLL\Sigma^*$.
Every ancestor outside these cones has a fixed branch reply;
every other subtree, including all expanded ground leaves,
is the same for the two sources. Within $LL$ the two subtrees
are $\rho^n b_1$ and $\rho^n\beta$; within $RLL$ they
are $\rho^{n+1}b_1$ and $\rho^{n+1}\beta$.
Lemma 7.2 forces a distinguishing word to have length at least

$$
2+\lceil n/2\rceil
\quad\text{or}\quad
3+\lceil(n+1)/2\rceil,
\tag{CRF.24}
$$

respectively. Both are at least $d_N$. The actual run on $u_*$
contains this read, regardless of any earlier reads or updates.

Make the separate comparison of that same run on $u_*$ with
the run on $u_y$. Before its first differing reply the epoch is
again common for that comparison. A distinguishing word now
must be in $LR\Sigma^*$ or $RRL\Sigma^*$, with compared
exponents $n$ or $n+2$. Its minimum length is at least
$2+\lceil n/2\rceil$ or $3+\lceil(n+2)/2\rceil$, again
at least $d_N$. These cones are disjoint from the two $x$ cones.
Thus the two required first-difference reads on the single
$u_*$ run are distinct. Their individual comparison epochs
need not coincide. Both lower bounds hold at every forward
epoch, which proves the joint assertion.

In particular this is not an addition of marginal worst cases:
the one fixed $u_*$, independent of the service, pays both
necessary lengths. $\square$

**Theorem 7.4 (exact six-hole joint frontier and weighted price).** On
the entire fiber (CRF.19), for every authentic $N\ge2$,

$$
\boxed{
\mathcal B_6=\{(2,0,4+2\lceil N/2\rceil)\},
\qquad
W_\lambda^*=2\lambda_q+
                   (4+2\lceil N/2\rceil)\lambda_\ell
}
\tag{CRF.25}
$$

for all rational nonnegative weights, including every zero-weight
face. The comparison is with all legal adaptive serial services
and arbitrary forward update counts.

Proof. The two actual static reads already supplied by ARH23.2
are

$$
LL\,R^{\lceil N/2\rceil},\qquad
LR\,R^{\lceil N/2\rceil}.
\tag{CRF.26}
$$

Each has complete physical length $d_N$.
At positive even $N$ their replies
$\alpha,\beta,\mathsf{branch}$ identify the corresponding
original subtree's three root cases. At odd $N$, the reply
groups $\mathsf{absent}$, $\alpha$, and
$\{\beta,\mathsf{branch}\}$ identify respectively
$\alpha$, $\beta$, and branch. These are the supplied
known-existing-subtree root decoders; no unknown-root guard
is assumed.

To state their complete output, the six reached addresses are
exactly $Q$, the outside is

$$
\left\langle\langle\square_1,\square_2\rangle,
 \left\langle\langle\square_3,\square_4\rangle,
                   \langle\square_5,\square_6\rangle\right\rangle
                                      \right\rangle,
\tag{CRF.27}
$$

and the partition is generated by

$$
\begin{array}{c|c}
x=\alpha&1=4,\ 3=6\\
x=\beta&1=6\\
y=\alpha&2=4\\
y=\beta&2=6 .
\end{array}
\tag{CRF.28}
$$

Use the entire equivalence relation generated by the applicable
rows. ARH (CE.23.12) proves that these exhaust the fifteen
unordered comparisons on the entire $D_6$; the constraints may
exclude combinations but never require an extra comparison.
Hence the two decoded root cases give the entire row for every
source, not just the three lower-bound witnesses. This static
service has sourcewise cost $(2,0,2d_N)$ on every source.

Conversely, Lemma 7.3 proves on the same actual source $u_*$
that every correct comparator has

$$
q_A(u_*)\ge2,\qquad \ell_A(u_*)\ge2d_N,
\qquad a_A(u_*)\ge0.
\tag{CRF.29}
$$

This also applies to comparators with unbounded worst costs:
their individual $u_*$ run is finite by legality.
Every finite feasible worst vector therefore dominates
$(2,0,2d_N)$, and every same-source weighted supremum is at
least $2\lambda_q+2d_N\lambda_\ell$.
The two-read service attains both bounds. This proves the
complete singleton Pareto basis and all stated weighted optima.
The lower proof does not need the epoch cap and includes
arbitrarily many source-dependent forward updates. $\square$

The old acquired relations are essential. Deleting only the three
negative records of (CRF.19) leaves the entire
$\{u(x,y):x\ne y\}$ with the same target. ARH Proposition 23.3
already supplies finite full-fiber bad pairs at every original
depth and proves no uniform raw budget there, even for serial
services. That negative theorem is reused, not rederived from
the present price calculation.

## 8. Native meaning of the added relation and exact reuse

The finite-marker bridge joins two already distinct forms of
information. The tree predicates describe the complete jointly
constrained source; the word predicates describe the one physical
action available to the internal observer. Complete-source
quantification precedes word synchronization. This order lets
constructor offsets differ without separating the source domain
into independent coordinate languages.

The resulting extra inference is Theorem 3.4: arbitrary finite
constructor reconstructions of aligned residual domains admit
effective common-word reachability and wrong-row predicates.
Its hypotheses are met by every accepted ARH constructor-elimination
chart, with arbitrary residual trees. Theorem 4.2 makes that
inference operational against every legal bounded comparator;
Theorem 4.3 retains the actual complete word lengths.
The JRF optimizer then applies because its missing source/action
premises have been supplied, not because its literal-only
language has been extended by analogy.

Doing nothing leaves ARH's sufficient static budget and its
existence criterion, with no exact price interface. Direct reuse
of SRF settles only the shared-header synchronous family.
Direct reuse of CAR settles the charts satisfying its forced
atomicity criterion. Neither supplies common actions for arbitrary
constructor offsets with unforced arbitrary residual trees.
The finite-marker conversion is sufficient for that particular
missing interface; it does not require a stronger interpreted
equation solver or a replacement source representation.
The exact native result (CRF.25) is a consumer beyond the
unmodified synchronous-frontier recognizer, by ARH23.2's
all-chart eligibility and strictness proof.

This is a relation between retained memory, an original boundary
task and the physical read/update/length resources of recovering
it. It does not identify physical time with update count, working
memory with a tree parameter, or a row with the original source.
The row can forget arbitrarily much source structure. The service
output also supplies no new access cut: retained old records and
new actual receipts continue to refine any future fiber unless
a separately supplied retention interface makes them inaccessible.
The actual producer remains ARH Proposition 2.1 at its finite
sourcewise paid scope. No equality acquisition or uniform
pre-cut price is obtained from the short retained signs.

## 9. Remaining full-domain obligation and evidence boundaries

**Open problem 9.1 (arbitrary acquired cyclic domains).** Keep arbitrary
finite $R,H_0,H_{\rm rel},Q,N$ under ARH Assumption 1.3 and
$D\ne\varnothing$, without the constructor-elimination,
synchronous or atomic recognizers. Decide whether a finite original
prefix determines the entire $R_Q$ and, when it does, compute the
full paid feasibility/frontier and same-source weighted interface
for all legal native competitors.

The missing general premise is an exact effective treatment of
the remaining coupled interpreted finite-tree equations and
disequalities, together with their whole-row prefix boundedness.
For example a residual equation
$\rho^a(x)=\langle A,B\rangle$ is not made aligned merely
by treating $\rho$ as a free constructor or rejecting its cycle:
$\rho(\beta)=\langle\beta,\alpha\rangle$ is a finite
solution of the corresponding self-reference. A failed
$\mathcal E_{\rm CE}$ recognizer is neither a negative
recovery answer nor an undecidability certificate.

Lemma 2.2 applies when an actual WS2S formula with only finitely
many free positions has been obtained. It does not create such
a formula for an arbitrary cyclic signed domain, nor does it
supply negative stopping for its original-prefix question.
Theorem 4.2 invokes the already proved ARH22.1 stopping criterion
before constructing its whole-row labels. Thus no unrestricted
decision follows from this companion.

ARH §§27–32 separately decide arbitrary cuts and arbitrary finite
literal refinements on the entire graph
$F(y)=\langle\rho(y),y\rangle$, including target comparisons
outside the earlier recognizers. Theorem 30.2 and Corollary 31.1
supply that recovery boundary and lawful sufficient paid service;
they are covered suppliers. This companion does not reprove that
arbitrary-cut theorem or automatically extend its minimum prices
outside the hypotheses of Definition 1.1.

**References 9.2 (suppliers and precise boundaries).** Repository
statement numbers refer to the source files in the immutable
[baseline catalogue][BASE]. The listed ordinary results are
reused at their stated hypotheses.

| Source | Used conclusion and limit |
| --- | --- |
| [ARH §§1–3, 19–25][ARH] | Exact acquired full fiber, paid producer and access assumptions; accepted elimination charts with arbitrary finite residuals; both prefix implications; productive original-prefix decision; complete six-hole fiber and supplied upper consumer. No general cyclic interpreted decision is presumed. |
| [ARH §§27–32][ARH] | Entire one-step graph with arbitrary literals and cuts; exact original-prefix recovery decision and sufficient lawful service. It is not a minimum-resource supplier for all those cuts. |
| [SRF Lemma 1.4, Proposition 1.5, §§2–3][SRF] | Aligned WS2S source/reply run encoding and determining-cell label construction; common-header synchronous resources. Here only the aligned formula and cell arguments are reused, with the new marker/word interface replacing common headers. Counterexample 1.6 excludes a direct-convolution shortcut. |
| [JRF Lemma 2.2, Theorem 3.1, Lemma 3.2, §§5, 7][JRF] | All-source length-nonincreasing transport, actual update cap, cleanup, finite cofinal rectangle and rational same-source threshold optimization. Its literal-only source predicates are not applied to the signed domain. |
| [ABC §§5–8][ABC] | Whole-source coordinate correspondence, opaque actual ports, sourcewise paid normalization, and the distinction between supplied-prefix testing and unbounded decision. No access to hidden canonical codes is introduced. |
| [CAR §§2–10][CAR] | Its cycle-mass recognizer, exact joint atomic charts and paid resource interface. Forced atomicity is its premise; arbitrary residuals here use no atomic-rank substitution. |
| [TPO Definition 1.2 and §§4–5][TPO] | Obstruction for its exact normal-domain language only. It supplies no undecidability or native no-service theorem for the present sources. |
| [SLH Theorem 2.2 and §§59, 74][SLH] | Current-epoch decoding of original literals, full old-row meaning and serial-to-prefix locality. These are actual read interfaces, not historical receipts or free subtree tests. |
| N. Klarlund and A. Møller, [MONA Version 1.4 User Manual §§7.1–7.2, pp. 39–40][MONA] | `literature-attested`: binary-tree positions, finite set variables, and bottom-up automata deciding WS2S and producing finite examples. Lemma 2.2 proves the additional marker-to-word conversion used here. |

The only general logical supplier required is WS2S on finite sets
with its finite support-tree automata. Product, determinization,
finite-state reachability and the fixed-prefix word tests are
given explicitly above. No appeal is made to closure under
unmatched presentations, arbitrary word equations with length
arithmetic, a stronger term-power language, infinite-tree
satisfiability or Dickson finiteness as a stopping algorithm.

**References 9.3 (formal-source comparison and limits).** The following
public and private declaration contracts were inspected as source
evidence; no current compiled application is claimed.

| Declaration source | Exact mismatch with this task |
| --- | --- |
| [SourceTransportCentralizer, `source_transport_centralizer`][D5-CENTRAL] | Classifies pairing-preserving maps commuting with substitution and their injectivity/image inverse. It does not decide coupled acquired fibers or optimize actual serial read words. |
| [ActualTreeReadoutAcquisition, `readout`, `Policy`, `paid`, `source_foundation`][D5-READ] | Actual four-valued fixed-source readout and source rigidity; its `paid` counts distinct addresses and its strategy target is fixed-source membership. It is not the raw-call/update/full-row resource contract here. |
| [ActualExactTraceCompiler, `strategy_exact_run`, `strategy_admissible`, private `exact_actual_prefix_replay`, `execute_suffix`][D5-TRACE] | Supplied coarse-factorizing strategies, allowed-source bounds and replay hypotheses; exact fixed-source traces do not supply common-word synthesis on (CRF.2). |
| [FirstWindowBoundaryAdaptive, `original_first_window_adaptive_price`, private `fiber_lower`][D5-WINDOW] | Requires $m\ge5$, prescribed finite phase sets, binary branch targets and allowed block histories. It concerns those window records, not arbitrary free-tree signed fibers. |
| [FiniteCommonMarginalSupermodular, `common_marginal_supermodular_le_diagonal`, private `clipped_increment_le`][D5-MARGINAL] | Finite linearly ordered coordinates, a probability mass with four equal marginals, and a supermodular test. It supplies no deterministic source/action correspondence here. |
| [Pinned mathlib `Computability/DFA.lean`][MATHLIB-DFA] | `DFA`, `eval`, `accepts` and the finite-state pumping interface concern ordinary word automata. They do not themselves supply the finite-tree/marker/native observation translation proved above. |

The mathlib source comparison uses revision
`db584cd6d46c92f209a44c0f1c829460d327499d`.
These are scoped source comparisons, not exhaustive library absence
claims. Adjacent stochastic restart or scan-runtime statements
require their external-stream and law hypotheses; no iid stream,
external producer or finite scanner-runtime promise is inserted
into this deterministic finite-tree problem.

**Status 9.4 (ordinary results and outstanding scope).** The
finite-marker conversion, shared physical-word construction,
their exact constructor-family paid applications, and the
single-source six-hole lower bound are `repo-derived` ordinary
results proved in this volume. The inherited recovery decision,
operational normalization and finite optimization schemes are
explicitly reused. No literature-wide novelty or priority claim
is made.

The exposition uses the repository formal-thinking and
theory-volume-template conventions within ordinary-theory
authorization. These proofs have one scientific author; this
text asserts neither independent approval nor a Lean build.
No finite experiment, implemented solver, practical complexity
bound or physical realization is offered as evidence for its
universal claims. The exact paid access contract remains
conditional on actual acquisition and the stipulated complete
accessible state. The unrestricted obligation in Open problem
9.1 and the broader continuing relation/recovery programme are
not completed by this increment.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SRF]: RECURSIVE_RELATIONAL_OBSERVATION_SYNCHRONOUS_RESOURCE_FRONTIER.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[MONA]: https://www.brics.dk/mona/mona14.pdf
[BASE]: https://github.com/the-omega-institute/trureturing/tree/8e1082af82ef26d8d8e9fe85fe3738908f2f5a1f
[D5-CENTRAL]: https://github.com/the-omega-institute/trureturing/blob/8e1082af82ef26d8d8e9fe85fe3738908f2f5a1f/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[D5-READ]: https://github.com/the-omega-institute/trureturing/blob/8e1082af82ef26d8d8e9fe85fe3738908f2f5a1f/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[D5-TRACE]: https://github.com/the-omega-institute/trureturing/blob/8e1082af82ef26d8d8e9fe85fe3738908f2f5a1f/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.lean
[D5-WINDOW]: https://github.com/the-omega-institute/trureturing/blob/8e1082af82ef26d8d8e9fe85fe3738908f2f5a1f/D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAdaptive.lean
[D5-MARGINAL]: https://github.com/the-omega-institute/trureturing/blob/8e1082af82ef26d8d8e9fe85fe3738908f2f5a1f/D5/S3/Combinatorics/Probability/FiniteCommonMarginalSupermodular.lean
[MATHLIB-DFA]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Computability/DFA.lean

## 追加锚（本行以下为增补区）
