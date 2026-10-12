# Native ambient contact synthesis and the joint-prefix alternative

## 1. Native objects and exact source hypotheses

**Definition 1.1 (native values and prefixes).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle,
\qquad T_n=\rho^n\alpha.
$$

Original values belong to the nonempty finite ordered tree algebra
$\mathcal T$. Its completion $\widehat{\mathcal T}$ also allows infinite
branches. At every reached node the reply is $\alpha$, $\beta$, or branch;
below a leaf it is absent. Write $s\equiv_h t$ when the four replies agree
at every original address of length at most $h$, inclusively. The unique
tree with a branch at every address is $\Omega$.

Fixed powers of $\rho$ are supplied natural numerals, with no common bound
across inputs. A repeated variable always denotes one whole value. The
extension of $\rho$ to completion trees uses these same local rules.
Pairing and each fixed power preserve $\equiv_h$. For pairing this follows
by passing to corresponding children. For $\rho$, matching leaf roots have
identical complete finite images, and matching branch roots reduce the
claim to the children at one smaller depth. Induction on $h$, followed by
iteration, proves the assertion, including absent replies.

**Definition 1.2 (the exact-cover hypothesis).** Fix a complete acquired
input $I$ in the language of [NIC, Definition 4.1][NIC] and a finite set
$B$ of distinct attained complete target rows, with $|B|\ge2$. For each
$r\in B$, let $D_r$ be its entire original-source stratum. Use the finite
cover of [NIC, Theorems 3.2, 3.3 and 4.3][NIC]:

$$
\begin{aligned}
C_{r,b}(n,z)&:=P_{r,b}(n)\land\Delta_{r,b}(n,z),\\
D_r&=\bigcup_{b\in\mathcal B_r}
 \{U_{r,b}(n,z):n\in\mathbb N^{k_{r,b}},\ z\in\mathcal T^{m_{r,b}},
                         \ C_{r,b}(n,z)\}.
\end{aligned}
\tag{NAC.1}
$$

Here $P$ is an effectively presented Presburger formula, and $\Delta$ is
the entire retained finite conjunction of native disequalities. Every
source map and every side of a disequality is a finite mixed template

$$
A::=g\mid T_{n_j+c}\mid\rho^a z_i\mid\langle A,A\rangle,
\qquad a,c\in\mathbb N,
\tag{NAC.2}
$$

where $g$ is a fixed finite native tree. Before the negatives the residual
domain is the full Cartesian product $\mathcal T^m$. Declared unused
coordinates remain in that product. Accidental equalities between distinct
names are allowed; repetitions of a name are shared.

Both directions of (NAC.1) are essential hypotheses. Every parameter tuple
satisfying $C_{r,b}$ reconstructs an actual member of $D_r$. Every member
of $D_r$ has a preimage reconstructing that same original source. Thus the
cover retains the old reached cut, its complete exterior and equality
partition, every actual-epoch literal, both reached guards for either sign,
every off-task relation, every image/rank condition in the input language,
and the complete target row. These conditions are enforced on finite
originals through the exact cover. They are not newly inferred at a limit.

NIC3.2 supplies the Cartesian positive images, NIC3.3 keeps native negatives
after expansion, and NIC4.3 supplies the entire acquired-source directions.
The warnings in [SLP, Sections 1 and 7][SLP] about a residual domain with
uneliminated positive constraints do not remove this explicitly supplied
exact-cover hypothesis. An additional predicate outside the NIC language
requires an exact normalization into (NAC.1); it is not silently admitted.

**Definition 1.3 (the simultaneous question).** Put

$$
J_B(h)\quad\Longleftrightarrow\quad
\exists (u_r)_{r\in B}\in\prod_{r\in B}D_r\quad
\forall r,s\in B\quad u_r\equiv_h u_s.
\tag{NAC.3}
$$

The tuple is simultaneous. Its components are alternative originals with
separate parameter tuples. No equality between different originals' hidden
values is an input condition. Within any one original all sharing remains.
The witnesses may change with $h$.

## 2. Ambient codes and exhaustive native branches

**Definition 2.1 (integer-labelled ambient codes).** Let $\mathscr C_{\mathbb Z}$
be the finite or infinite full ordered binary trees whose leaves have labels
$[j]$, $j\in\mathbb Z$. Let $F$ denote raw ordered pairing. The unique
leafless code is $O$; it is an infinite tree, not a leaf or an additional
constant label. In particular $F(O,O)=O$ extensionally. For $d\in\mathbb Z$,
let $\sigma^d$ add $d$ to every finite leaf label and preserve all pair nodes.
It fixes $O$, is a group action, and commutes with $F$.

A code is admissible if all its leaf labels are nonnegative. Write
$\mathscr C_{\mathbb N}$ for these codes. Expansion is

$$
E([j])=T_j,\qquad E(F(C,D))=\langle E(C),E(D)\rangle,
\qquad E(O)=\Omega.
\tag{NAC.4}
$$

This defines expansion at every finite address: follow raw pairs until a
code leaf is met, then follow its finite native tree. At a requested finite
depth only finitely many raw pairs are visited. Thus expansion is also
well-defined on infinite codes. It need not be injective:
$E(F([1],[0]))=E([2])$.

**Lemma 2.2 (native coverage and the leafless period).** For admissible
$C,D$ and $a\ge0$,

$$
E(F(C,D))=\langle E(C),E(D)\rangle,
\qquad E(\sigma^aC)=\rho^a E(C).
\tag{NAC.5}
$$

A code is finite if and only if its expansion is finite. Every native
completion $u$ has an admissible code $B(u)$ satisfying

$$
E(B(u))=u,\qquad B(\rho^a u)=\sigma^a B(u).
\tag{NAC.6}
$$

For a native pair, either

$$
\begin{aligned}
B(\langle u,v\rangle)&=F(B(u),B(v)),\quad\text{or}\\
B(u)&=[q+1],\quad B(v)=[q],\quad
B(\langle u,v\rangle)=[q+2]\quad(q\in\mathbb N).
\end{aligned}
\tag{NAC.7}
$$

Finally, for every code $C\in\mathscr C_{\mathbb Z}$ and $d\ne0$,

$$
C=\sigma^dC\quad\Longleftrightarrow\quad C=O.
\tag{NAC.8}
$$

**Proof.** The expansion identities follow at each finite prefix from the
native recurrence $T_{j+2}=\langle T_{j+1},T_j\rangle$, distribution, and
$T_{j+a}=\rho^aT_j$. A finite code expands to a finite tree. An infinite
finitely branching code has an infinite branch, whose raw pair nodes remain
native pair nodes after expansion, so its expansion is infinite.

The coding in (NAC.6) is the semantic coding of [NIS, Theorem 9.2][NIS]
and [ABC, Theorems 2.2--2.3][ABC]. Its precise construction is useful here.
Replace every maximal finite atomic subtree $T_j$ by $[j]$ and retain all
other pair nodes. These maximal subtrees are disjoint. Every finite native
leaf lies in one, since it is itself $T_0$ or $T_1$, and its finite list of
ancestors contains a highest atomic subtree. A subtree with no finite leaf
is the unique leafless full tree. Therefore the construction defines one
admissible code on all finite addresses, and expansion recovers $u$.

For clarity about the shift identity, $\rho$ preserves infinite branches
and is injective on completions. Its possible root images are disjoint:
a preimage $\alpha$ gives $\beta$, a preimage $\beta$ gives
$\langle\beta,\alpha\rangle$, and a pair preimage gives a pair both of
whose children are $\rho$ images and hence have root different from
$\alpha$. Prefix induction in the last case proves injectivity. It follows
that $\rho u$ is atomic precisely when $u$ is atomic; the atomic rank then
increases by one. In the reverse direction rank zero is not a $\rho$ image,
and $T_j=\rho T_{j-1}$ for $j\ge1$. Thus maximal atomic subtrees are
translated without changing the retained pair structure. This proves the
shift identity, first for one step and then for $a$ steps.

If the whole native pair is atomic, its rank is at least two and the
recurrence and pair injectivity force exactly the second case of (NAC.7).
Otherwise its root pair is retained. When both children are leafless the
first case holds as $F(O,O)=O$; no separate leafless branch is needed.
No effective recovery of $B(u)$ from an arbitrary infinite input is asserted.
It is used to cover solutions, not to compute them.

If $C$ has a finite leaf at address $p$ with label $j$, equality to
$\sigma^dC$ would give $j=j+d$ at that same address. This is impossible
for $d\ne0$. A full tree without leaves is $O$, which every shift fixes.
This proves (NAC.8). $\square$

**Definition 2.3 (finite positive completed presentations).** A presentation
has finitely many declared completed variables, positive equalities, and
finite displayed terms using fixed finite grounds, $\Omega$, pairing,
fixed numeral powers of $\rho$, and atoms $T_{a(p)}$. Here $p$ is a finite
natural tuple and each $a$ is an affine integer expression with an explicit
nonnegativity guard. Include every declared variable, even if unused.
Image conditions $X\in\rho^e(\widehat{\mathcal T})$, if present, mean
$X=\rho^eY$ with an additional declared completion variable $Y$. This is
an existential image statement, not a finite-preimage condition.

Flatten just the displayed finite syntax. Distribute fixed powers through
displayed pairs and atoms if necessary, and expand finite grounds into their
finite native syntax. Each subterm has a slot in a fixed finite set $S$;
repeated names reuse a slot. Every displayed pair supplies a record
$Z=\langle X,Y\rangle$ with its existing children $X,Y\in S$.

For each such record choose one of two cases:

$$
Z=F(X,Y),\qquad\text{or}\qquad
X=[q+1],\ Y=[q],\ Z=[q+2],\quad q\in\mathbb N.
\tag{NAC.9}
$$

There are finitely many choices. In a case, the remaining records have the
forms

$$
C_s=\sigma^d C_t,\quad
C_s=F(C_l,C_r),\quad
C_s=[a_s(p,q)],\quad C_s=O.
\tag{NAC.10}
$$

All equality offsets $d$ are fixed integers. All finite rank expressions
are affine in the finite parameters $(p,q)$. There is no normality or
noncollapse guard on a raw pair record. No original negative is translated
into ambient code inequality.

**Lemma 2.4 (two source directions for the code branching).** Every solution
of a positive native presentation in Definition 2.3 supplies a branch of
(NAC.9) with an admissible valuation of every slot at the same original
finite parameters. Conversely every admissible valuation of one branch
expands to a solution of that native presentation.

**Proof.** Evaluate every displayed native subterm and code it with $B$.
Use (NAC.7) at every displayed pair. Genuine finite collapses supply their
natural $q$; all other pairs choose the raw case. Equations and fixed powers
are respected by (NAC.6). Thus all named subterms, including repeated and
unused names, have simultaneous admissible codes in one branch.

Conversely expand all slots. A raw pair record is sound by (NAC.5); a
collapse record is sound by the actual atomic recurrence. A shift record
is sound because its original positive power is nonnegative, and its inverse
orientation merely expresses the same code equality. Finite atoms and $O$
expand as prescribed. Induction through the finite named syntax reconstructs
every original equality. Dropping normality creates overlapping native
solutions, not extra nonsolutions. Expansion injectivity is never used.
$\square$

## 3. Finite congruence on the displayed slots

**Definition 3.1 (weighted components).** For one fixed branch, maintain a
weighted forest of equalities among the slots in $S$. Each component has a
representative $v$ and integer potentials $\delta_s$ expressing

$$
C_s=\sigma^{\delta_s}V_v,\qquad \delta_v=0.
\tag{NAC.11}
$$

A component may additionally be marked leafless. A mark means that every
slot in it has value $O$. In an unmarked component every equality processed
so far has its indicated relative potential. In a marked component all
integer offsets are semantically irrelevant, since shifts fix $O$.

To impose $C_s=\sigma^dC_t$, merge different components with the potential
required by $\delta_s=d+\delta_t$ after their representatives are related.
If the components already agree and this equality of potentials fails,
mark the component leafless. If either of two merged components was marked,
the merged component is marked. An explicit $O$ record marks its component.
Keep every original leaf and pair descriptor attached to its original slot.

For pair descriptors $p=F(l,r)$ and $p'=F(l',r')$ with parents in the same
unmarked component, impose both equations

$$
C_l=\sigma^{\delta_p-\delta_{p'}}C_{l'},
\qquad
C_r=\sigma^{\delta_p-\delta_{p'}}C_{r'}.
\tag{NAC.12}
$$

For a pair descriptor whose parent is marked, mark both child components.
A component with a leaf descriptor and a pair descriptor is inconsistent,
and a marked component with a leaf descriptor is inconsistent. For two
leaf descriptors in the same unmarked component retain the arithmetic
condition

$$
a_s(p,q)-\delta_s=a_t(p,q)-\delta_t.
\tag{NAC.13}
$$

**Theorem 3.2 (closed finite obligation universe and saturation).** These
operations have a terminating saturation schedule on the original slot set
$S$. They preserve exactly the admissible valuation relation of the fixed
branch, with the retained arithmetic conditions. They introduce no new
child slots or displayed pair descriptors.

**Proof.** A merge rewrites the same equality using a common representative.
A nonzero potential cycle gives $C=\sigma^d C$, $d\ne0$, so (NAC.8) makes
its mark necessary and sufficient for that cycle. Every equality in a
marked component then holds for all its offsets. A marked parent of a raw
pair is $O$ if and only if both its children are $O$. Raw pair injectivity
and commutation with $\sigma$ give exactly (NAC.12). A shifted pair has a
branch root; a shifted leaf has a leaf root, so the stated clashes are
impossible. Two shifted leaf descriptors are equivalent to (NAC.13).
Each transformation therefore preserves the full valuation relation;
parallel descriptors are kept, rather than replaced by a selected one
without their consequences.

Here is an explicit finite schedule. Reserve the input shift equations,
the two cancellation keys for every unordered pair of displayed pair
descriptors, the two mark-propagation keys for every displayed pair,
the descriptor clashes, and all unordered pairs of leaf descriptors.
This is a finite obligation universe determined before saturation.
Initially impose the input shift equations and explicit marks. Scan all
reserved structural keys. When an operation merges two components or
marks a previously unmarked slot, restart the scan. If a full scan produces
no such change and no clash, structural saturation is finished. Read all
leaf equalities (NAC.13) with the final potentials.

There are at most $\max\{|S|-1,0\}$ component merges. The number of marked
slots increases and is at most $|S|$. Thus at most
$|S|+\max\{|S|-1,0\}$ change-triggered restarts are possible, followed by
one unchanged scan. In the empty presentation case, there are no keys and
the initial scan is already unchanged. Each scan has only the finitely many
reserved keys. An equation within an unmarked component
whose offset agrees with the potentials requires no restart. One whose
offset disagrees marks that component and is counted as a change.

This also justifies rescanning weighted keys. Once two slots are connected
in an unmarked component their relative potential cannot change under a
later forest attachment: both receive the same added representative offset.
A later contradictory equation marks that component. If the parent component
is marked, all children of every one of its pair descriptors are eventually
marked, so its parallel pair equations hold at $O$. Consequently neither
changing representatives nor a later mark leaves an unprocessed parallel
condition. Arithmetic leaf conditions may be read at the end; changes of
representative subtract the same offset from both sides of (NAC.13).

Cancellation in (NAC.12) only refers to children already in a displayed
record. There is no rule that splits a descriptor-free slot into a new pair.
All pair-root information needed for native coverage was selected in
(NAC.9). This is the difference from imposing reduced-code root cases on
new children. It proves finite closure as well as termination, with no
assumed bound on a slot-generating procedure. $\square$

## 4. Arithmetic admissibility and a selected completed solution

**Definition 4.1 (the final weighted constructor graph).** In a saturated
unmarked component choose one of its leaf or pair descriptors if present.
The clashes exclude having both. A leaf descriptor $t$ gives

$$
V_v=[\ell_v(p,q)],\qquad \ell_v=a_t-\delta_t.
\tag{NAC.14}
$$

A pair descriptor $p_0=F(l,r)$ gives

$$
V_v=F(\sigma^{w_L}V_{v(l)},\sigma^{w_R}V_{v(r)}),
\qquad w_L=\delta_l-\delta_{p_0},\quad
w_R=\delta_r-\delta_{p_0}.
\tag{NAC.15}
$$

These are directed edges with fixed integer weights. Marked components
are assigned $O$. A component with no descriptor is free and is also
assigned $O$ for the selected solution. A pair component remains a pair
equation, including when it belongs to a constructor cycle. In particular,
a terminal-free recursive component is not removed from the graph merely
because it has no displayed leaf.

Unfold (NAC.15) down finite words, adding weights, and use (NAC.14) when
a terminal is reached. Free and marked states unfold as $O$. Every edge
out of a pair consumes one address letter; hence this defines one code
$V_v^*$ for each state. It may have infinitely many differently labelled
leaves. It is a finite weighted representation, not a claim that the expanded
native tree has finitely many distinct subtrees.

**Theorem 4.2 (finite exact all-path admissibility).** Suppose structural
saturation has no clash. There is an effectively constructed Presburger
guard $A(p,q)$, conjoined with the original finite-atom and natural-collapse
guards, such that the following are equivalent at each $(p,q)$:

1. the branch has an admissible code valuation on every declared slot;
2. the selected unfolding $C_s^*:=\sigma^{\delta_s}V_{v(s)}^*$ is admissible
   on every slot and satisfies every branch record;
3. $A(p,q)$ holds.

A branch with a negative-weight constructor cycle from which a terminal is
reachable is discarded. For every other branch, let $d(v,t)$ be the minimum
weight of a directed path from $v$ to terminal state $t$, when reachable,
including a path of length zero. Apart from (NAC.13) and the initial guards,
$A$ consists exactly of

$$
\ell_t(p,q)+\delta_s+d(v(s),t)\ge0
\quad\text{for every }s\in S\text{ and reachable terminal }t.
\tag{NAC.16}
$$

**Proof.** Any solution of the branch has the forest relations (NAC.11).
Saturation has reconciled every parallel pair descriptor by both child
equations. Thus choosing one descriptor gives (NAC.15) without forgetting
another definition. A discarded relative-potential discrepancy has a
leafless component; all corresponding shifted values are $O$, so the
reconciliation still holds there. Leaf descriptors agree precisely when
(NAC.13) holds.

Following any directed path $\pi$ to terminal $t$ in any solution forces
an actual code leaf with label

$$
\ell_t(p,q)+\delta_s+\operatorname{wt}(\pi)
\tag{NAC.17}
$$

when the starting slot is $s$. This statement is proved by induction on
the path length using (NAC.15), and does not depend on free-state values.
Every graph state contains a representative slot, so every negative cycle
is reachable from a slot. If it can reach a terminal, traverse it $N$ times
before taking a path to that terminal. Its negative weight makes (NAC.17)
negative for sufficiently large $N$, at every fixed finite $(p,q)$. No
admissible solution exists in this case.

Otherwise, in the subgraph from which a terminal is reachable, there are
no negative cycles. For fixed endpoints, removing cycles never increases
the weight of a path. The minimum is therefore attained by a path with
no repeated vertex, or the empty path. This supplies an entirely finite
way to compute every $d(v,t)$: enumerate those finitely many simple paths.
The same finite cycle enumeration decides the preceding negative-cycle test.
No shortest-path termination hypothesis is being assumed.

Every path weight is at least its computed minimum, so nonnegativity of
all forced labels (NAC.17) is equivalent to the finite list (NAC.16).
It is necessary in every admissible valuation. The initial affine guards
and (NAC.13) are also necessary.

For sufficiency take the selected unfolding. Assigning free states $O$
introduces no leaf. Its remaining leaves are exactly the finite paths to
the retained terminals. Equations (NAC.16)--(NAC.17) make every such leaf
nonnegative in every original slot, not only at the common output. All
shift relations follow from the forest, with marks handling inconsistent
cycles; all pair records follow from the reconciled descriptors; all
leaves follow from (NAC.13). Marked pair records have both children $O$.
Hence every branch record holds and every slot is admissible.

The guard is a finite conjunction of affine integer equalities and
inequalities in natural parameters. This is Presburger. Components with
negative cycles having no path to a terminal impose no leaf-label
inequality; their selected unfolding is permitted. They are not rejected
by a finite-tree occurs check. The argument proves all three equivalences.

The distinctions can also be seen directly on native equations. For
$\rho X=\langle X,\alpha\rangle$, the collapse branch has $q=0$ and
$X=[1]$, retaining the actual finite witness $X=\beta$ of
[NIC, Proposition 3.4][NIC]. The raw branch instead gives
$X=F(\sigma^{-1}X,[-1])$ and fails admissibility. For
$\rho X=\langle\alpha,X\rangle$, the collapse branch would require
$0=q+1$ with $q\ge0$; the raw branch gives
$X=F([-1],\sigma^{-1}X)$. Both fail. For
$\rho X=\langle X,X\rangle$, the raw branch is
$X=F(\sigma^{-1}X,\sigma^{-1}X)$: its negative cycles have no terminal,
and its selected value is $O$, expanding to the valid $\Omega$.
These evaluations use the all-path guard just proved, rather than a
free-unary occurs check. $\square$

**Theorem 4.3 (finite-coordinate preservation).** For a fixed surviving
branch, compute the selected value of each original declared variable.
Its set $F_*$ of finite coordinates is independent of the parameter values
satisfying $A$. Every such coordinate is a finite mixed native template
$f_i(p,q)$. At the same finite parameters every admissible solution of
that branch has exactly this value on $F_*$. All other selected coordinates
are infinite.

Consequently every original completed native solution is covered by a
selected solution, at the same original finite parameters, whose finite
original coordinates are a subset of that original solution's finite
coordinates and have the same values there.

**Proof.** A selected slot is finite precisely when the graph reachable
from its state has no directed cycle and reaches neither a marked state
nor a free state. If these conditions hold, its reachable graph is a
finite acyclic graph ending only in leaf descriptors. Unfolding it gives
a finite code expression. Equations (NAC.14)--(NAC.15) force this expression
in every branch solution, regardless of the values at free states.

If a free or marked state is reachable, its selected $O$ supplies an
infinite branch. If a directed cycle is reachable, following that cycle
indefinitely supplies an infinite pair path. Thus every failure of the
stated finite criterion produces an infinite selected code. Lemma 2.2
makes its native expansion infinite as well. Finite labels cannot remove
an existing raw infinite pair path.

For a finite slot, unfold its acyclic graph starting with its actual
$\delta_s$. Each resulting leaf has an affine integer rank, nonnegative
under $A$ by Theorem 4.2. Native expansion gives $f_i(p,q)$. To express
this in the nonnegative grammar (NAC.2), give each of its finitely many
leaf occurrences a fresh natural scalar $b$ and the affine equality
$b=\ell_t+\delta_s+\operatorname{wt}(\pi)$. Replace that leaf by $T_b$.
These auxiliary scalars have unique values at each $(p,q)$ satisfying
$A$; repetitions of the resulting whole template are unchanged.

Finally, start with any original native completed solution. Lemma 2.4
chooses a branch and finite collapse ranks from it. Its code valuation
survives Theorems 3.2 and 4.2. Any coordinate finite in the selected
solution is forced by the acyclic calculation, so is the same finite
coordinate of the starting solution. Optional finite coordinates may
become infinite when a free state is assigned $O$; no new finite coordinate
is introduced and no retained finite value changes. $\square$

**Corollary 4.4 (effective positive contact selector).** Every finite
presentation of Definition 2.3 has an effectively constructed finite list
of guarded weighted graphs. It has a completed native solution precisely
when some graph guard has a natural solution. Each accepted graph gives
one selected native solution and its finite-coordinate templates. All
finite requested prefixes of that solution are computable.

**Proof.** Combine Lemma 2.4 and Theorems 3.2--4.3, then decide the finitely
many Presburger guards. For prefix computation at depth $h$, start at the
requested slot with its potential. Follow at most $h+1$ raw pair levels
on any path. A free or marked state gives branch replies indefinitely.
At a reached terminal compute its affine label plus the accumulated
weight; admissibility guarantees a natural number. Compute the required
prefix of the finite $T_j$ there by the native recurrence. Although a
representative in isolation can have negative labels, every reached
terminal with its actual starting-slot potential has a nonnegative label.
No negative-index native tree is evaluated. The computation visits finitely
many nodes and terminates.

For the supplied non-rational contact
$X=\langle\alpha,\rho X\rangle$ of [SPC, Theorem 4.2][SPC], the raw
graph is $C=F([0],\sigma C)$. Its left leaf at $R^jL$ has label $j$.
Thus its expansion has the pairwise distinct finite subtrees $T_j$ at
those addresses. The finite weighted representation computes its prefixes
without asserting rationality of the native expansion. $\square$

## 5. Whole signed support after selecting finite coordinates

**Definition 5.1 (joint masks and completed contact presentation).** Choose
one chart $b_r$ for each $r\in B$. Choose a subset $K_r$ of its original
scalar coordinates to diverge. Let $c_r$ be the natural values of the
complement, and write $\lambda_r=(c_r,\infty_{K_r})$. Extend the source map
by replacing $T_{n_j+d}$ with $\Omega$ for $j\in K_r$, and by its literal
finite atom for $j\notin K_r$. The justified limit is $T_n\to\Omega$:
if $m(n)$ is the minimum leaf depth, $m(0)=m(1)=0$ and
$m(n+2)=1+\min(m(n+1),m(n))$, so $m(n)=\lfloor n/2\rfloor$.

Introduce one common completion variable $W$ and all original chart
residual variables $\eta_{r,i}$. Form the single positive presentation

$$
\widehat U_{r,b_r}(\lambda_r,\eta_r)=W\qquad(r\in B).
\tag{NAC.18}
$$

Different rows initially have separately named scalar and residual tuples.
Every occurrence within one row keeps its name. Apply Corollary 4.4 to
this whole presentation. A branch $\tau$ gives a guard $A_\tau(p)$,
a selected contact, a set $F_{r,\tau}$ of finite original residuals,
and templates $f_{r,\tau}(p)$. The tuple $p$ contains all original finite
$c_r$, collapse ranks, and the natural leaf-rank auxiliaries of Theorem 4.3.
All of these are fixed before a depth or lower bound is requested.

Let $w_r$ contain all original scalar coordinates in $K_r$, including
ones absent from the displayed source map. Restore the original rank
vector as $n_r(c_r,w_r)$. In the *finite* chart substitute just
$f_{r,\tau}(p)$ on $F_{r,\tau}$, leaving its other original residuals as
unrestricted finite variables $z'_r$. Define the entire support

$$
\Psi_{r,\tau}(p,w_r)\quad\Longleftrightarrow\quad
P_{r,b_r}(n_r(c_r,w_r))\ \land\
\exists z'_r\in\mathcal T^{\overline F_{r,\tau}}\quad
\Delta_{r,b_r}(n_r(c_r,w_r),f_{r,\tau}(p),z'_r).
\tag{NAC.19}
$$

The cross-row completed equalities (NAC.18) are not added to (NAC.19).
They select the prefixes toward which finite witnesses are lifted; finite
originals need only agree through the requested depth.

**Lemma 5.2 (uniform arithmetic support and forgetting finite coordinates).**
Each predicate (NAC.19) has a uniform effective Presburger formula in
$(p,w_r)$, on $A_\tau(p)$. If an original contact has a larger finite
residual tuple $f_r$ agreeing with $f_{r,\tau}(p)$ on $F_{r,\tau}$, its
entire finite support is contained in (NAC.19) at every original rank tuple.

**Proof.** The uniform formula is exactly the supplied parametric-template
interface [FNS, Corollary 2.6][FNS], or equivalently [SFS, Lemma 5.1][SFS]
with [URR, Theorem 3.1 and Corollary 3.2][URR]. Its hypotheses hold because
Theorem 4.3 supplies a finite syntax of nonnegative rank atoms and pairs,
and every remaining residual has the full Cartesian domain before the
entire original negative conjunction.

More explicitly, substitute those finite templates in every occurrence.
The resulting finite list has the URR mixed grammar with scalar variables
$(p,w_r)$. Its one residual separator is uniform over these scalars. After
that substitution all comparisons are between finite templates of atoms.
Bottom-up normal pairing branches finitely on whether two primitive
children have ranks $a=b+1$; in that case they collapse to $[b+2]$.
Otherwise their raw pair remains a normal node. In each arithmetic branch
normal-code equality is equality of the finite shapes and corresponding
ranks. Taking the native complements for the whole negative list and
conjoining $P$ gives the desired Presburger formula. No arbitrary finite
barrier tree is encoded by an assumed integer parameterization; the finite
templates have already been forced by the contact graph.

For support inclusion, any finite witness with all of $f_r$ fixed still
has the selected subset fixed. Its other formerly fixed values may simply
be used as values of $z'_r$. It satisfies the same $P$ and the same entire
$\Delta$. This proves inclusion pointwise, before taking a scalar closure.
$\square$

**Definition 5.3 (the finite decision sentence).** For a chart tuple, scalar
mask tuple and surviving code branch $\tau$, put

$$
\mathsf G_\tau\quad\Longleftrightarrow\quad
\exists p\in\mathbb N^{d_\tau}\quad
\left[
 A_\tau(p)\ \land\
 \forall M\in\mathbb N\ \exists (w_r)_{r\in B}\quad
 \left(
  \bigwedge_{r\in B}\Psi_{r,\tau}(p,w_r)
  \ \land\ \bigwedge_{r\in B}\bigwedge_{j\in K_r} w_{r,j}\ge M
 \right)
\right].
\tag{NAC.20}
$$

Let $\mathsf G(I,B)$ be the disjunction of these sentences over all finite
chart choices, all scalar masks, and all surviving branches. There are
finitely many of each. The tuple of divergent ranks is one simultaneous
tuple in (NAC.20). In particular, a support $w_1=0\lor w_2=0$ does not pass
its positive simultaneous lower bounds even though each marginal is
unbounded. Empty tuples and empty conjunctions have their usual singleton
and true meanings. With no divergent ranks the inner condition is ordinary
finite support nonemptiness.

## 6. Source-faithful total classification

**Theorem 6.1 (full native joint-prefix synthesis and stopping).** Under
Definition 1.2, the effectively constructed Presburger sentence satisfies

$$
\mathsf G(I,B)\quad\Longleftrightarrow\quad
\forall h\in\mathbb N\ J_B(h).
\tag{NAC.21}
$$

There is therefore a total mathematical procedure on the finite input
$(I,B)$ with the following alternatives:

- it returns a finite $H$ with $\neg J_B(H)$; or
- it returns a represented common completed contact and, on every requested
  finite $h$, actual simultaneous finite originals $(u_r)_{r\in B}$ with
  $u_r\in D_r$ and $u_r\equiv_h u_s$ for all $r,s\in B$.

The procedure preserves every finite-source condition in (NAC.1), including
every signed guard and the entire old and target rows. It has no supplied
contact oracle, rank bound, source sample, or rational-native-contact
restriction.

**Proof (necessity).** Suppose $J_B(h)$ holds for every $h$. Choose finite
witness tuples at increasing depths, and choose one exact-cover preimage
of each original component. There are finitely many joint chart choices.
One chart tuple occurs at an unbounded sequence of depths; keep it.

The completion-tree space is compact. Indeed, at each depth there are
finitely many four-reply patterns; repeated subsequence selection and a
diagonal subsequence give compatible finite prefixes. Their limit is a
full finite or infinite native tree. The scalar space
$\overline{\mathbb N}=\mathbb N\cup\{\infty\}$ is also sequentially compact:
a natural-number sequence has a constant subsequence or a subsequence
tending to infinity. These arguments apply to the finite product of all
parameter coordinates in all retained charts. Thus a further joint
subsequence converges to $((\lambda_r,\eta_r))_{r\in B}$.

Every finite scalar limit is eventually its exact value $c_{r,j}$.
Every finite residual limit is eventually its exact finite native tree:
replies through one more than its height isolate that tree. All other
residual limits have an infinite branch. The source maps are continuous
by Definition 1.1 and $T_n\to\Omega$. Their limits therefore satisfy one
common equation (NAC.18), since the original source outputs agreed through
unbounded depths along the subsequence.

Let $F_r$ be all finite residual coordinates of this contact, with values
$f_r$. For each simultaneous lower bound $M$, sufficiently late subsequence
terms have every finite coordinate stabilized and every divergent scalar
above $M$. Their finite parameters still satisfy all original $P$ and
$\Delta$. They give the whole cofinal support with $f_r$ fixed. This is
the necessary direction of [FNS, Theorem 5.2][FNS] and [SLP, Theorem 3.1][SLP]
applied to the exact NIC cover, rather than a sign assigned to a limit.

Code this completed contact using Lemma 2.4. The selected branch has the
same original finite $c_r$ and definite natural collapse ranks. Theorems
4.2--4.3 provide accepted finite parameters $p$ and selected finite sets
$F_{r,\tau}\subseteq F_r$, with the same actual finite values there. The
pointwise support inclusion in Lemma 5.2 shows that the cofinal witnesses
with all $f_r$ fixed still witness every $\Psi_{r,\tau}$ after the optional
finite coordinates are forgotten. The same $p$ precedes every $M$.
Consequently (NAC.20) holds for this branch, proving $\mathsf G(I,B)$.

This step is the reason setting a genuinely free ambient component to $O$
is legitimate here. It is done after positive contact saturation, and its
only change to the finite-barrier antecedent is to enlarge the entire
feasible support. No arbitrary positive finite-source equation is being
passed to SLP as a disequality-only constraint.

**Proof (sufficiency and finite originals).** Suppose a sentence (NAC.20)
holds, and choose one satisfying finite $p$. Corollary 4.4 gives computable
native completions $\eta^*_{r,i}$ and $W^*$ satisfying (NAC.18). Exactly
the residual coordinates in $F_{r,\tau}$ are finite; they have the supplied
actual values $f_{r,\tau}(p)$. Every other selected residual has an infinite
branch.

Fix an inclusive depth $h$. Compute the depth-$h$ prefixes of all these
infinite residuals. Require every divergent original rank to be at least
$M=2h+2$. Then every occurrence of its atom $T_{w_{r,j}+c}$ has only branch
replies through depth $h$, as does $\Omega$. Fix all original finite ranks
at their components of $p$, and fix the finite residuals exactly. Pairing
and fixed $\rho$ powers preserve inclusive depth-$h$ agreement, so these
parameter requirements suffice to make every source map agree with $W^*$
through depth $h$. They also suffice inside arbitrarily repeated or shifted
occurrences of any residual name. A smaller local depth would sometimes
suffice; this common one is finite and valid.

The inner condition of (NAC.20) supplies one tuple $(w_r)_r$ satisfying
all supports at this same bound. At each row's chosen ranks and finite
residuals, (NAC.19) supplies a finite residual seed for the whole negative
conjunction. Apply [SLP, Lemma 2.1 and Corollary 3.2][SLP] to that row,
prescribing the computed prefixes of its infinite coordinates. Its
hypotheses hold: the remaining residual product is Cartesian, every
prescribed completion has a live frontier, the entire finite negative list
has a seed, and all finite residual coordinates have been fixed.

SLP supplies one finite residual tuple satisfying every listed negative
and every prescribed prefix together. Its holes are independent only
between distinct residual names; repeated occurrences use the same
context and same filling. Different rows can use separate finite fillings.
They are alternative originals, and their completed contact equations are
not required as exact equalities on the finite fillings.

Evaluate the actual native source maps at these finite parameters. By the
forward direction of (NAC.1), the resulting $u_r$ lies in the entire $D_r$.
It therefore retains the complete old exterior and partition, every literal
at its actual epoch, both guards for each signed relation, all off-task
constraints, all retained image/rank conditions, and its exact target row.
By the prefix calculation each $u_r\equiv_h W^*$, hence every pair of them
agrees through $h$. This gives one simultaneous witness tuple for (NAC.3).
No signed condition or finite row partition has been asserted of $W^*$.
For example the supplied finite native inequality $z\ne\rho z$ has
finite prefix witnesses toward $\Omega$, although
$\Omega=\rho\Omega$. Explicitly $P_0=\alpha$,
$P_{d+1}=\langle P_d,P_d\rangle$, with $d>h$, has the required branch
prefix and is different from its $\rho$ image. The latter fact follows
from the strict increment of finite normal-code leaf ranks. The identity
negative $z\ne z$, in contrast, has empty finite support. This familiar
finite/limit distinction is enforced by (NAC.19), not by a negative test
on $W^*$.

Every requested-depth construction terminates: finite graph prefix
unfolding terminates; Presburger witness extraction supplies ranks; finite
NSF feasibility supplies seeds; SLP supplies finite prefix-preserving
fillings; and the source maps are finite syntax. The fixed $p$ and contact
are retained, while the actual finite witnesses can change with $h$.

**Proof (total classification and a failed finite depth).** Finite chart
normalization is supplied by NIC. Scalar masks and pair cases are finite.
Theorem 3.2 bounds saturation by finitely many scans. Theorem 4.2 gives a
finite cycle/path computation and a finite arithmetic guard. Lemma 5.2
gives a finite support compilation. Hence (NAC.20) is an effectively given
Presburger sentence. Its truth is decidable by [Ginsburg--Spanier,
Theorem 1.2][GS]; Theorem 1.3 also gives effective semilinear descriptions
if desired. Decide the finite disjunction $\mathsf G(I,B)$.

If it is true, choose an accepted branch and its finite $p$. Existence is
already decided, so enumeration of natural tuples with decidable membership,
or Presburger witness extraction, terminates. Use the positive construction
above on every requested depth.

If it is false, the proved necessity implication gives
$\exists H\ \neg J_B(H)$. For each specified $h$, the predicate $J_B(h)$
has a total finite-source decision with actual positive witnesses by
[NSF, Lemma 5.1 and Theorems 4.3, 5.2][NSF]. To spell out the multiway use,
enumerate the finitely many common four-reply tables through depth $h$.
For each table conjoin that same table with the complete finite native
predicate for each separate original source and its row. Fixed-address
navigation compilation produces a finite signed native formula on the
whole product. NSF decides it and reconstructs finite originals when
satisfiable. Thus all of $J_B(h)$ is decided, not only a selected source
sequence or a pairwise subproblem.

Starting at $h=0$, these terminating depth decisions eventually find a
failed $H$, because its existence has already been established by the
negative global decision. This extraction is not the proof of all-depth
stopping: that proof is the finite graph and Presburger decision, completed
before the search for $H$. Both alternatives therefore terminate on every
finite input satisfying Definition 1.2. No explicit uniform numerical
bound on the first failed depth or on runtime is needed for this conclusion.
$\square$

## 7. Exact supplier scope and recovery consequences

**Definition 7.1 (scope relative to the earlier interfaces).** Theorems
3.2--4.3 provide a finite ambient construction on displayed slots with all
parallel descriptors and all leaf-label inequalities. This is an
existential selector preserving forced finite original coordinates.
It does not prove a partition or parameterization of every completed
solution by finite integer tuples. In particular an unconstrained original
completion variable still has all of $\widehat{\mathcal T}$ as its solution
set; the selector merely chooses $\Omega$ for it.

Relative to [NIS, Definition 9.4 and Proposition 10.4][NIS], the raw-code
branching avoids unbounded reduced-root splitting, Theorem 3.2 supplies a
fixed obligation universe and scheduling argument, Theorem 4.2 supplies
arithmetic elimination for the selected graph, and Theorem 4.3 supplies the
finite-coordinate preservation needed for the signed bridge. Theorem 6.1
then provides the full common-output and total-stopping implications on the
complete NIC-covered class. It does not assert equivalence with every
reduced-code graph valuation, or supply a particular machine-readable
negative-certificate format mentioned in NIS10.4. Its negative output is a
finite failed $H$ decided by the existing finite-source theory.

[FNS, Theorem 5.2][FNS] already identifies all-depth original witnesses
with existence of a common completed map and an entire cofinal finite-profile
support. Its Corollary 2.6 supplies the arithmetic compiler for a supplied
finite template. The new step is synthesis of a sufficient template profile
and common map without being given either. [SLP, Lemma 2.1 and Theorem 3.1][SLP]
already supply independent live-prefix lifting and its exact closure
criterion; they are used after contact saturation, at exactly the finite
coordinates fixed by Theorem 4.3. [URR, Theorem 3.1 and Corollary 3.2][URR]
supply one simultaneous finite negative separator and entire scalar support,
not a replacement of the whole image by that section. The finite solver,
finite positive covers, signed lifting, and cofinal-support compiler remain
credited suppliers.

These statements are ordinary mathematical deductions from the displayed
native laws and the stated supplier interfaces. They make no claim of
current kernel verification or literature priority.

**Definition 7.2 (primary arithmetic and unification comparisons).**
S. Ginsburg and E. H. Spanier, *Semigroups, Presburger Formulas, and
Languages*, Pacific Journal of Mathematics 16(2), 285--296,
[Theorems 1.2--1.3][GS], supplies the literature-attested decidability and
effective semilinear conversion used only after the explicit native
elimination. It says nothing about unknown native completed values before
that elimination.

A. M. Marshall, C. Meadows and P. Narendran, *On Unification Modulo
One-Sided Distributivity: Algorithms, Variants and Asymmetry*,
[Sections 4--5, Theorems 4.4 and 5.8][MMN], supplies a comparison with a
single homomorphism distributing over a binary operation. Their
subterm-collapse-free finite-unifier setting is not the present native
leaf algebra or its completion. In particular their finite occurs-check
reasoning cannot discard a completed native constructor cycle, and it
cannot replace the atomic branches forced by $\rho\beta=
\langle\beta,\alpha\rangle$. No unification algorithm or complexity bound
is imported from that paper. The finite ambient closure and the native
source directions are proved above instead.

**Corollary 7.3 (boundary, record, source and transport).** For a fixed
complete input and attained finite $B$, the retained memory predicates and
native transport determine which of the two alternatives in Theorem 6.1
holds for original boundary replies. In its positive case, no finite
original-prefix depth distinguishes all rows of $B$ on their entire
strata. In its negative case, the returned depth excludes that one
simultaneous family; for $|B|>2$ it need not distinguish every pair in $B$.

For a supplied finite entire row image, apply Theorem 6.1 to every distinct
row pair. If all pair alternatives are negative, the maximum of their
finitely many returned depths determines the complete row throughout the
entire source fiber. If one pair alternative is positive, no such finite
determining depth exists. Under the paid complete-state assumptions of
[ARH][ARH], this is the source-level boundary used by the existing
original-prefix/service correspondence.

**Proof.** The first assertion is (NAC.3) and Theorem 6.1. Pairwise
prefix determination on a finite row image is equivalent to exclusion of
every distinct row pair. Agreement through a larger depth implies agreement
through every smaller one, so the finite maximum suffices in the all-negative
case. A positive pair supplies counterexamples at every depth. This uses
the whole row strata, with no selected finite source catalogue. $\square$

**Definition 7.4 (observer and programme boundaries).** Completion values,
integer code labels, weighted graphs, masks and scalar witnesses are
mathematical coordinates. They are not observer ports. The acquired
complete-state cut and paid source-total producer are supplied as in ARH;
none of the constructions certifies or acquires that physical state for
free. There is no inverse-$\rho$, equality, clone, reset, reroot or rank
operation added to the observer. The result gives no optimum for reads,
address length, physical time, retention or acquisition costs, and no
minimality conclusion from the two leaf symbols. The broader recovery
programme beyond the declared native exact-cover class remains separate.

[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[FNS]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_NATIVE_COFINAL_SPECTRA.md
[NIS]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_SATURATION.md
[SFS]: RECURSIVE_RELATIONAL_OBSERVATION_SYMBOLIC_FEEDBACK_SYNTHESIS.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[MMN]: https://arxiv.org/html/1503.06687v2

## 追加锚（本行以下为增补区）
