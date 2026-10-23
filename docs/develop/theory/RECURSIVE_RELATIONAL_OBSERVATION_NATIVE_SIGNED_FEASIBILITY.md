# Native signed feasibility and bounded observation interfaces

This volume proves an existential decision theorem for the actual finite
Fibonacci tree algebra. Its application decides fixed original-prefix
questions and finite read/update/address-length boxes on entire acquired
signed fibers. Two additional invariance certificates give complete
bounded-recovery decisions within their stated domains. The unrestricted
existence-of-prefix and unbounded-physical-word decisions remain separate
obligations.

All proofs here are ordinary mathematics. No implemented solver, Lean
compilation, physical execution, complexity guarantee or independent
approval is asserted.

## 1. The native algebra and the acquired interface

**Definition 1.1 (finite native syntax).** The domain and operation are

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&
\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle x,y\rangle&=\langle\rho x,\rho y\rangle .
\end{aligned}
\tag{NSF.1}
$$

Every tree is nonempty, finite, ordered and free. A native expression is
built from variables, these two constants, native pairing and operations
$\rho^k$ for supplied natural numerals $k$. Expressions may nest these
operations. An existential native problem is

$$
\exists x_1,\ldots,x_n\in\mathcal T\quad\Phi(\mathbf x),
\tag{NSF.2}
$$

where $\Phi$ is any finite quantifier-free Boolean combination of
equalities of native expressions. There is no bound on the variables'
tree sizes. A numeral exponent is not an existentially quantified epoch;
a fixed physical word used below is not a quantified arbitrary word.

**Assumption 1.2 (the whole retained fiber).** Use exactly [ARH,
Assumption 1.3][ARH]. The full old row $R$ at a finite prefix-free original
cut $P$, every finite literal record in $H_0$, and every finite signed
relation record in $H_{\rm rel}$ jointly define

$$
D=\{u:R_P(u)=R,\quad H_0(u),\quad H_{\rm rel}(u)\}.
\tag{NSF.3}
$$

Service assertions assume $D\ne\varnothing$. For a signed record
$e=(a,s,b,t,\bowtie)$ its meaning is

$$
s\in\operatorname{Pos}(\rho^a u)\ \land\
t\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_s\ \bowtie\ (\rho^b u)|_t,
\qquad \bowtie\in\{=,\ne\}.
\tag{NSF.4}
$$

Absence invalidates both signs. The entire concrete old exterior,
repeated old classes, all cross-class and off-task disequalities, all
guards and all further records stay on the same original source.

The records were acquired before the complete access cut. The supplied
accessible state has exactly fiber (NSF.3); source-bearing caches,
lengths, addresses, control, timing, permissions and archives cannot
retain an unlisted distinction. Entry is the actual original-root
register $\rho^N u$ with authentic $N$ at least every acquired epoch.
The paid sourcewise acquisition of [ARH, Proposition 2.1][ARH] supplies
this interface under its complete-state assumption; it does not promise
a uniform acquisition cost.

The target $R_Q(u)$, for finite prefix-free original $Q$, retains the
reached cuts, the entire concrete exterior with numbered holes, and
their complete whole-subtree equality partition. In particular the
empty cut outputs the complete source; the root cut outputs one hole.

**Definition 1.3 (paid comparison class).** Services are common
deterministic effective controllers correct and terminating on every
$u\in D$. Their source operations are actual physical
$\mathsf{Read}(p)$ at any finite original-root word, forward same-register
$\mathsf{ApplyRho}$, and absorbing $\mathsf{Halt}$. A reply may select
the next action. There is no equality, chart, source-identity, reset,
reroot, clone or unknown-tree port. Set

$$
\begin{aligned}
c_A(u)&=(q_A(u),a_A(u),\ell_A(u)),&
\ell_A(u)&=\sum_{\text{actual reads at }p}|p|,\\
b(A)&=(\sup_Dq_A,\sup_Da_A,\sup_D\ell_A),&
W_\lambda(A)&=\sup_{u\in D}\lambda\cdot c_A(u).
\end{aligned}
\tag{NSF.5}
$$

Here $q$ counts every raw read, including repeated and absent replies,
and $a$ counts actual post-entry updates. Root reads cost one call and
zero literal length. The nonnegative rational weights in $W_\lambda$
are applied to each finite sourcewise run before the supremum.
Different coordinate maxima need not occur on one source.
Computation, installation, address generation, memory, authentication,
retention, output and physical time remain separately supplied resources.

**Convention 1.4 (proof falsifiers).** The correspondences below require
both original-source directions. An ambient witness that is not a normal
native code falsifies the algebraic reduction. A missing endpoint that
passes a signed test falsifies its history application. Two sources
sharing a proposed terminal observation but having different reached
cuts, exteriors or partition bits falsify behavioral sufficiency.
A backward epoch, free semantic selector or fictional receipt falsifies
the consumer correspondence. A larger cost on any same source falsifies
a claimed sourcewise dominance. Excluding a legal adaptive comparator
falsifies an optimum claim. An unbounded search without an independent
negative stopping argument falsifies a decision claim. These are proof
obligations; finite examples do not establish the universal statements.

## 2. Reused normal coordinates and a finite flattening

**Definition 2.1 (the supplied normal algebra).** Reuse [ABC, Theorems
2.2–2.3][ABC]. Its ambient codes and normal subdomain are

$$
\mathcal K::=[n]\ (n\in\mathbb N)\mid F(\mathcal K,\mathcal K),
\qquad
F(X,Y)\in\mathcal N
\ \Longleftrightarrow\
X,Y\in\mathcal N\ \land\
\neg\exists j\ge0\ (X=[j+1]\land Y=[j]).
\tag{NSF.6}
$$

Every primitive $[n]$ is normal. The two effective inverse maps are
$B:\mathcal T\to\mathcal N$ and $E:\mathcal N\to\mathcal T$, with
$E([n])=T_n=\rho^n\alpha$. Native pairing corresponds to

$$
J(X,Y)=
\begin{cases}
[j+2],&X=[j+1],\ Y=[j],\\
F(X,Y),&\text{otherwise},
\end{cases}
\tag{NSF.7}
$$

and $\rho^k$ corresponds to $\tau_k$, addition of $k$ at every
primitive leaf, preserving $F$. Translation preserves normality and
its image consists exactly of normal codes all of whose ranks are at
least $k$. In particular $\rho$ is injective. These facts are reused,
not new normal-form theorems.

**Definition 2.2 (flattened branches).** Convert (NSF.2) into a finite
disjunction of conjunctions of equations and disequations. Give every input
variable and every subexpression a code name, consistently retaining
repeated variables.
Its defining constraints have the forms

$$
Z=[0],\quad Z=[1],\quad Z=\tau_kX,\quad Z=J(X,Y).
\tag{NSF.8}
$$

An original signed atom becomes equality or disequality between its
names. Definitions remain positive even when the original atom is
negative. Every name must denote a normal code.

For each of the finitely many $J$ definitions choose one of two branches.
The collapse branch imposes $X=[r+1],Y=[r],Z=[r+2]$ for a natural scalar
$r$. The other branch imposes $Z=F(X,Y)$ and requires normality.
No ordinary-constructor branch is admitted with a forbidden primitive
cherry. Choices for different occurrences are made jointly.

**Lemma 2.3 (exact finite branch reduction).** The native problem has
a solution if and only if one flattened branch has a solution by normal
codes and natural scalars. Native solutions extend to such a branch by
evaluating every subexpression. Conversely expansion of a branch's
variable codes gives a native solution of the original Boolean formula.

Proof. The maps $B,E$ identify equality in the native algebra with
equality of normal codes. They also identify its constants, pairing and
fixed iterates with (NSF.8). For a normal pair of arguments the two cases
of (NSF.7) are exhaustive and exclusive. A noncollapse branch's normal
output excludes exactly the collapse pattern. Induction through the
finite expression graph therefore proves its definitions, with the same
value at every repeated name. Propositional disjunctive normal form
preserves truth, including complements. Both source directions follow.
$\square$

Flattening is not a replacement of $\rho$ by a free unary constructor.
For example $\rho x=\langle x,\alpha\rangle$ has the native witness
$x=\beta$. In its collapse branch all three involved codes are
primitive. Treating the outer symbols of the unnormalized native
expression as free constructors would discard that witness.

## 3. Shape equations and the information left on their leaves

**Definition 3.1 (shape unifier).** Erase primitive ranks, writing
$c$ for a primitive shape and $f$ for the free binary shape constructor.
Each flattened branch has finite shape equations: primitive definitions
force shape $c$, $Z=\tau_kX$ forces equal shapes, ordinary pairing
forces $s_Z=f(s_X,s_Y)$, and positive code equalities force equal shapes.
Disequalities impose no shape equation.

Solve these equations by finite first-order unification over $c,f$,
with the ordinary finite-tree occurs check. A failure rejects this
branch. Otherwise take an idempotent most general unifier and write
$S_Z$ for the resulting finite shape term of each name. Its remaining
shape variables are $w_1,\ldots,w_m$. Every solution of the shape
equations factors through these terms by ground finite shapes. This is
ordinary syntactic unification of free shapes, not native unification.

Decorate each explicit $c$ occurrence in $S_Z$ with a scalar rank
variable $r_{Z,p}$. Decorate each occurrence of $w_j$ with a block
variable $U_{Z,p}$ of shape $w_j$. Occurrences at different positions
have different decorations, even if the shape variable is the same.
Repeated use of the same code name reuses the same decorated template.
Let this finite template be $\widehat S_Z$.

**Lemma 3.2 (complete remaining equation forms).** Comparing the
decorated sides of every positive equation produces only

$$
r=r'+d,\qquad r=d,\qquad U=V+d,
\tag{NSF.9}
$$

with fixed integer offsets, together with scalar nonnegativity.
In the last equation $U,V$ have the same residual shape $w_j$ and
$+d$ denotes pointwise rank addition. An equation involving a fixed
rank is interpreted with its actual natural value. Collapse equations
supply their stated scalar offsets. No equation connects a residual
block to an explicit scalar, or blocks of different $w_j$ sorts.

Proof. Shape unification has made the two sides of every required code
equality syntactically the same shape term. For a shift equality,
traverse those identical terms; each corresponding $c$ compares two
scalar ranks and each corresponding $w_j$ compares two whole rank
functions on that same shape. For $Z=F(X,Y)$, compare $S_Z$ with
$f(S_X,S_Y)$, which are also syntactically identical, and do the same
traversal with offset zero. Positive equalities are identical traversals.
A primitive definition has shape $c$. There is consequently no
comparison of a $c$ with a residual variable or of different residual
variables. Cancellation of offsets merely writes these constraints in
(NSF.9). Every original positive equation is recovered by reassembling
its compared leaves. $\square$

**Definition 3.3 (finite normality and negative requirements).** Impose
$r_{\rm left}\ne r_{\rm right}+1$ at every explicit cherry in every
$\widehat S_Z$, meaning a node with two explicit $c$ children.
For a code disequality $X\ne Y$:

- if $S_X,S_Y$ are syntactically different, retain it as a shape-separation
  requirement;
- if they are identical, decompose the disequality into the finite
  disjunction of unequal corresponding scalar ranks or unequal
  corresponding blocks.

Distribute these latter disjunctions. Each resulting branch has scalar
offset equations and disequations, and whole-block offset equations and
disequations. Writing offsets on both sides instead of one makes no
difference. A reflexive disequality yields an empty successful
disjunction and rejects its branch.

Normality has not yet been asserted for arbitrary fillings of the
residual shapes. The next section supplies a restricted witness family
and proves its sufficiency. It does not erase that obligation.

## 4. Finite witnesses for the unconstrained residual shapes

**Lemma 4.1 (shape separation with nonleaf markers).** For a finite list
of shape terms over $c,f,w_1,\ldots,w_m$, one can effectively choose
pairwise distinct ground shapes $G_1,\ldots,G_m$, all nonleaf and all
having the same number $M$ of leaves, so that substitution
$w_j\mapsto G_j$ preserves every syntactic inequality in that list.

Proof. Choose $M\ge2$ larger than every listed term's leaf count
(counting variable occurrences as leaves), and large enough to have
at least $m$ distinct full ordered binary shapes with $M$ leaves.
This is effective. For example, for $M\ge3$ there are at least $M-1$
shapes, obtained by taking a root whose left and right combs have
$i$ and $M-i$ leaves, $1\le i<M$. Increase $M$ to satisfy both bounds
and enumerate that finite family.

To compare unequal terms, cancel matching root constructors until the
first disagreement. Different variables receive distinct markers.
A variable has substituted leaf count $M$, while $c$ has one.
A compound subterm containing no variable has fewer than $M$ leaves.
A compound with at least one variable has more than $M$ leaves: it
either has two variable occurrences, or one and at least one other
leaf. Thus a variable cannot become equal to such a compound. A
constant/compound disagreement remains a constructor disagreement.
These exhaustive cases prove simultaneous separation. $\square$

The equal-mass separation principle is standard and is also used by
[NativeGroundSeparation][D5-GROUND]. That module marks native Boolean
leaves. The argument here specifies the required one-constant *shape*
markers and their nonleaf boundary condition; it is not an application
of a Boolean-leaf marker after silently erasing its distinguishing labels.

**Lemma 4.2 (constant-rank replacement for residual blocks).** Fix one
residual shape sort. Suppose its finite whole-block offset equations
and disequations have a solution by natural-valued functions on the
leaves of some nonempty finite shape. They then have a solution by
constant natural-valued functions on any prescribed nonempty finite
shape. All finitely many residual sorts can be treated simultaneously.

Proof. Make a graph whose vertices are block names and whose equation
$U=V+d$ imposes a difference of $d$. Following edges, with their signs,
expresses every vertex in a connected component as

$$
U=B_C+\delta_U.
\tag{NSF.10}
$$

A cycle with nonzero total offset is impossible even at a single leaf.
Thus a functional solution implies that every cycle has zero offset.
Potentials $\delta_U\in\mathbb Z$ can be computed by a finite traversal.

A disequation between vertices of the same component is impossible if
their prescribed offsets make its two sides equal; otherwise it holds
at every leaf. A disequation between different components forbids just
one difference between their constant bases. Choose component bases
successively, each larger than all lower bounds required by
$B_C+\delta_U\ge0$, and avoiding the finitely many forbidden values
arising from already chosen components. Infinitely many natural
choices remain. This gives the requested constant functions and
satisfies every disequation simultaneously. Different shape sorts have
no connecting constraints by Lemma 3.2. $\square$

This argument uses whole-block equality and its negation. It would not
apply without further proof to arbitrary pointwise predicates demanding
different leaf locations, to comparisons between different positions
inside one unspecified block, or to universally quantified code
properties.

**Theorem 4.3 (terminating native existential decision and witnesses).**
There is a terminating YES/NO algorithm for every (NSF.2).
A YES answer produces concrete finite native values for all its free
variables. More explicitly, one can compute a finite list of finite
code templates, with only scalar natural ranks left unspecified, and
a finite arithmetic condition for each, such that a native solution
exists exactly when at least one arithmetic condition is satisfiable.
These templates are witness templates, not a representation of every
source in the solution fiber.

Proof. Perform §§2–3, rejecting failed shape unifications. For each
remaining negative branch choose the markers of Lemma 4.1 for all
shape terms of its code names. Replace every block occurrence of sort
$w_j$ by $G_j$ with a single scalar $b_U$ assigned to all its leaves.
The same block name uses the same scalar everywhere.

Keep all scalar constraints from §§2–3. Translate $U=V+d$ and
$U\ne V+d$ into $b_U=b_V+d$ and $b_U\ne b_V+d$. Require every scalar
rank nonnegative and impose normality at each explicit template
cherry. The result is a finite conjunction of integer offset equalities,
disequalities and lower bounds, hence an effectively decidable
Presburger formula. Offset equations can alternatively be eliminated
by the finite potential calculation in Lemma 4.2; no tree oracle is
required by this arithmetic step. A satisfying arithmetic assignment
is effectively obtainable.

For an explicit arithmetic stopping procedure, add one distinguished
scalar of value zero and express each fixed-rank equation by an edge
to it. Compute integer potentials in every equation component.
Reject an inconsistent cycle, a negative forced rank in the anchored
component, or a disequation whose two sides are forced equal in one
component. Every unanchored component has only a lower bound on its
base. Assign its base above that bound and outside the finitely many
values forbidden by disequations with already assigned components.
Treat the anchored component first. This finite procedure either
rejects for one of the stated necessary reasons or constructs all
ranks; remaining cross-component disequations are met when their
later component is assigned.

For soundness, every inserted marker has constant rank at all leaves.
Its cherries therefore have equal ranks and are normal. Its root is a
constructor, so insertion creates no primitive cherry across the
template/marker boundary. Every other possible primitive cherry is an
explicit one, whose inequality was imposed. All resulting code names
are thus normal. Lemma 3.2 reassembles every positive definition.
A shape-separated disequality follows from Lemma 4.1. Each remaining
disequality has its selected scalar or block mismatch. Lemma 2.3 now
expands these normal codes to an actual native solution.

For completeness, start with any native solution, with no size promise.
Its evaluation chooses a flattened branch and its finite code shapes
factor through the unifier in Definition 3.1. Read the actual scalar
ranks at the explicit leaves. They satisfy every explicit normality
constraint, since the actual codes are normal. For an identical-shape
disequality, at least one of its finitely many compared scalar leaves
or block occurrences differs; choose such a disjunct. The actual
decorations of each residual shape give a functional solution of all
its whole-block offset constraints, even if that residual shape happens
to be a single leaf. Lemma 4.2 replaces those functions by constants on
the chosen nonleaf marker. Scalar ranks at explicit leaves can be
retained. No scalar/block constraints were lost, by Lemma 3.2.
Replacing an originally primitive residual shape by a nonleaf can
remove a boundary cherry but cannot create one. The explicit normality
conditions still hold. Syntactically different shape terms are now
separated by Lemma 4.1. Hence this branch's arithmetic problem has a
solution.

There are finitely many propositional branches, finitely many collapse
choices, finite unification problems and finitely many negative
disjunct choices. Each arithmetic decision terminates, including its
NO case. Rejecting all branches therefore terminates and is correct
by completeness; it is not failed source enumeration. In a YES case
expand one returned normal assignment by $E$. This terminates and
provides the finite native witness. $\square$

**Corollary 4.4 (formula-dependent finite witnesses, exact image
conditions).** The algorithm imposes every image lower bound and every
normality condition needed by its witnesses. It supplies a computable
native witness-height bound depending on the input formula alone.
It supplies neither a uniform source bound on its entire solution set
nor a bound for a sequence of different formulas indexed by an unknown
prefix depth.

Proof. In an equation $Z=\tau_kX$, all ranks of $X$ are natural and the
corresponding ranks of $Z$ equal them plus $k$. This is exactly ABC's
image condition, not an unrestricted inverse translation. Theorem 4.3
proved normality at every occurrence. Its finite scalar problems have
effective decisions and witness extraction. Run those terminating
procedures for the finite template list and take the largest expanded
height among their chosen witnesses, taking zero when none exist.
This is a total computable bound and a witness exists under it precisely
when the formula is satisfiable. The finite template bound is obtained
before rank solving; ranks and expansion can be large. A formula such
as $x=x$ still admits every native tree. Nothing identifies a bounded
witness family with that full domain. $\square$

**Proposition 4.5 (why this is not the excluded domain interpretation).**
Theorem 4.3 does not define $\mathcal N$ by a uniform formula in the
ambient term-power language excluded by [TPO][TPO].

Proof. It modifies existential witnesses after finitely many shape
equations have been solved, using a marker size depending on those
equations and disequalities. It does not preserve every assignment,
every formula with alternation, or an arbitrary parameter code's
normality. Normality is proved directly for the finitely constructed
templates. Consequently no uniform ambient predicate defining all
normal codes, or canonicalization graph for arbitrary codes, is
obtained. Theorem 4.3 and TPO's exact-language obstruction have different
quantifiers and are compatible. $\square$

## 5. Fixed navigation, Boolean complements and whole-source queries

**Lemma 5.1 (finite native observation compilation).** Given finitely
many native expressions in finitely many source variables, supplied
epochs, supplied physical addresses, finite cuts and fixed concrete
row values, one can decide an existential Boolean combination of:

1. native expression equalities;
2. fixed-coordinate literal replies or reached tests;
3. guarded whole-subtree equalities and disequalities;
4. equality of a complete row to a fixed row, or equality of two
   complete rows at a fixed cut.

Negations are allowed. A positive existential answer gives values of
all original source variables. No physical word or epoch is quantified.

Proof. First distribute fixed iterates through the finitely many
explicit native constructors and evaluate their effects on constants.
Choose an original prefix depth strictly greater than every address
length used in navigation or a cut. Decompose each source variable
into all its finitely many original prefix patterns at that depth.
Each pattern has concrete early leaves and independent native
variables at its reached frontier. Repeated occurrences of the same
source variable use the same pattern and the same frontier variables.
These pattern/valuation pairs cover all finite source tuples exactly;
the inverse takes their actual original subtrees. This is the
decomposition used by [ARH, Proposition 3.2][ARH] and
[NativeDepthPatterns, depthEquiv][D5-DEPTH].

Along a fixed request no frontier variable is entered. Navigation
either stops in a known constructor term, yielding its entire remaining
native expression, or enters the explicitly computable finite iterate
of a known early leaf. In the latter case both reachability and the
whole reached tree are computed exactly. An absent path stays absent.
Literal labels are similarly determined. Thus a guarded comparison is
either false because a guard fails, or precisely the indicated native
expression comparison. Its Boolean complement is computed *after*
this guard handling. It is not obtained by flipping its sign.

For a cut $A$, keep its finite reached set and replace each reached
subtree by $\alpha$, obtaining a native mask expression $M_A$.
Keep every uncut residual subtree in this expression. With the
reached set fixed, this mask determines the entire hole context:
replace the subtrees at those known positions by numbered holes.
This is [ABC, Theorem 4.2][ABC], equally valid in native syntax.
Two rows are equal precisely when their reached sets agree, their
mask trees agree and every pair of reached holes has the same
whole-subtree equality bit. A fixed concrete row uses its filled mask
and its full stated partition. Therefore all row tests and their
complements become finite Boolean combinations of native equalities.
This retains an arbitrarily large concrete exterior as a term, rather
than reducing the target to its partition.

Apply Theorem 4.3 on each resulting pattern case. Fill its witness
frontiers to recover the original variable tuple. Conversely every
original tuple has its exact pattern case, with the identical
navigation, guards, masks and whole-subtree tests. These are both
domain directions. In particular no negated existential auxiliary
graph has been incorrectly pulled through a quantifier: Boolean
negation is performed only after deterministic case evaluation.
$\square$

**Theorem 5.2 (arbitrary signed fibers and opposite-sign feasibility).**
Emptiness of (NSF.3) is decidable, without its nonemptiness promise.
A nonempty answer supplies one finite original source satisfying
every retained constraint. The same holds after any finite Boolean
combination of fixed-coordinate tests, complete-row tests and tests
on fixed native transforms of one or more copies of the source.

Proof. Apply Lemma 5.1 to the complete predicate (NSF.3). In particular
the old row is tested as a complete row; equivalently use ARH's old
class filling with all pairwise cross-class disequalities and its
exact constructor reconstruction. All records share the same $u$.
For two-source questions use independent $u,v$, each satisfying the
*whole* retained predicate. Copies of $u$ inside its own records stay
shared. Witness reconstruction in Lemma 5.1 proves every record and
the concrete old exterior simultaneously. $\square$

For example, to ask whether a reached equality is forced, its
counterquery imposes both reach guards and the opposite equality bit
in addition to the full retained input. To ask whether the *guarded
positive predicate itself* is forced, its counterquery also permits a
failed guard. These are different questions. On $u=\beta$, the signed
record $(0,L,1,R,\ne)$ is false despite the second endpoint existing;
the negation of its guarded equality is true because the first endpoint
is absent. Lemma 5.1 keeps that distinction.

A witness returned here is an offline hypothetical source consistent
with the query. It is never identified with the actual source and is
never added as a source-bearing cache at entry.

## 6. Supplied-depth whole-row determination

**Theorem 6.1 (exact fixed-prefix decision).** For every input (NSF.3),
every finite prefix-free $Q$ and every supplied $h\ge0$, one can decide

$$
\operatorname{PrefDet}(D,Q,h):
\quad
\forall u,v\in D,\quad
\left(\forall |p|\le h,\ r_u(p)=r_v(p)\right)
\Longrightarrow R_Q(u)=R_Q(v).
\tag{NSF.11}
$$

A false answer supplies finite $u,v\in D$ with the stipulated common
prefix and different full rows. A true answer on nonempty $D$ gives
an effective actual static whole-row consumer at entry $N$.

Proof. There are finitely many words with length at most $h$. The
negation of (NSF.11) is an existential query on two whole sources:
both retained predicates, equality of each of their four-valued
literal replies at those words, and inequality of their complete rows.
Lemma 5.1 and Theorem 5.2 decide it and provide exactly its witnesses.

For a true answer use the paid historical decoder of [SLH, Theorem
2.2][SLH] to recover those original literal replies from actual epoch
$N$ reads. Each original request needs at most two current reads,
each of length at most $h+\lceil N/2\rceil$. There are
$2^{h+1}-1$ original requests. Conjoin their recovered original prefix
with the full retained predicate and use Theorem 5.2 to obtain a
source witness. The actual source proves this conditioned fiber
nonempty. Equation (NSF.11) makes the witness's full row the correct
output on that entire fiber. Halt genuinely after output. Only the
actual current queries produce receipts.

Alternatively precompute the finitely many prefix-conditioned
nonempty fibers and their constant row outputs; install the resulting
finite table. The decoder is source-total, uses no updates and has
upper budgets

$$
q\le 2(2^{h+1}-1),\qquad
a=0,\qquad
\ell\le 2(2^{h+1}-1)(h+\lceil N/2\rceil).
\tag{NSF.12}
$$

No optimum is asserted by these upper bounds. $\square$

This replaces the conditional feasibility premise of ABC's fixed-prefix
application by a native existential decision. It reuses ARH's
static/serial existence bridge; it does not replace $\exists h$ by a
finite search. If every supplied-depth test is false, successive finite
counterexamples alone give no algorithmic signal that all future tests
will also be false.

## 7. Finite physical service trees and exact finite boxes

**Definition 7.1 (finite serial skeleton).** A skeleton is a finite
four-reply tree with read vertices and absorbing halt leaves. Each read
vertex carries one fixed physical word $p_v$ and one fixed epoch $n_v$.
Epochs are at least $N$ and nondecreasing along each root-to-leaf path.
Before a read execute exactly the difference from the preceding actual
epoch by forward updates. Halts add no updates. For a leaf $t$ define

$$
\begin{aligned}
D_t&=\{u\in D:
 r_{\rho^{n_v}u}(p_v)=c(v,t)\text{ at every read ancestor }v\},\\
c_t&=(k_t,n_t-N,\sum_{v\prec t}|p_v|),
\end{aligned}
\tag{NSF.13}
$$

where $k_t$ counts read ancestors, $n_t$ is the last read epoch, and a
root halt has $n_t=N$. These are entire jointly constrained path fibers.

**Theorem 7.2 (finite-tree checking with actual terminal outputs).**
For a supplied skeleton, every $D_t$ has decidable emptiness and,
when nonempty, decidable constancy of the whole $R_Q$.
If all nonempty leaves are constant, one can effectively install their
correct row outputs, obtaining a source-total lawful service with exact
cost $c_t$ on every source in $D_t$.

Its exact worst-coordinate vector and exact same-source rational
weighted worst value are computable, and a finite original source
attaining each maximum can be returned.

Proof. Each path adds only finitely many fixed literal tests.
Theorem 5.2 decides its feasibility. Row nonconstancy is the
two-source query

$$
\exists u,v\in D_t\quad R_Q(u)\ne R_Q(v),
\tag{NSF.14}
$$

decided by Lemma 5.1. For each nonempty constant leaf take its returned
finite source witness and compute that witness's full row. Equation
(NSF.14)'s failure makes this the correct row on the entire $D_t$.
Empty leaves receive an arbitrary fixed output.

Induction on the actual reply sequence proves that execution follows
the unique path whose fixed tests the actual source satisfies. Its
epochs never decrease, every read uses its full literal original-root
word, and a halt ends the execution. The finite tree is source-total;
the actual source cannot reach an empty leaf. Its exact costs are
(NSF.13). Consequently

$$
b(A)=\left(\max_{D_t\ne\varnothing} k_t,\
\max_{D_t\ne\varnothing}(n_t-N),\
\max_{D_t\ne\varnothing}\sum_{v\prec t}|p_v|\right),
\qquad
W_\lambda(A)=\max_{D_t\ne\varnothing}\lambda\cdot c_t .
\tag{NSF.15}
$$

The saved mathematical witness for a maximizing leaf realizes that
cost. It need not be the witness maximizing a different coordinate.
No marginal source choices have been combined. $\square$

**Theorem 7.3 (exact supplied finite-box decision).** For arbitrary
$D$ under Assumption 1.2 and supplied integers $K,A,L\ge0$, it is
decidable whether any service of Definition 1.3 satisfies

$$
q_A(u)\le K,\qquad a_A(u)\le A,\qquad\ell_A(u)\le L
\quad\text{for every }u\in D.
\tag{NSF.16}
$$

A positive answer returns a finite lawful service meeting all three
bounds on the whole original fiber. The comparison includes all legal
effective adaptive serial services, with no uniform local running-time
promise.

Proof. Enumerate finite four-reply tree shapes of read depth at most
$K$, with early halts allowed, epochs in $\{N,\ldots,N+A\}$, and
physical words of length at most $L$. This is a finite enumeration,
including the empty word and absent addresses. Test each tree by
Theorem 7.2. Require its path sums and counts to meet (NSF.16) only
on nonempty leaves. A passing tree gives the positive consumer by
that theorem.

For the opposite comparator direction, take any service meeting
(NSF.16). At a reachable reply prefix, all initial accessible data and
acquired replies agree. Its next computation/update segment, next
read word or halt, and halt output are therefore fixed. At least one
source realizes that prefix. Source-totality on this source makes
that segment finite. A read bound $K$ leaves only finitely many
reachable reply prefixes. Unroll these segments into a finite tree,
replace unreachable children by immediate halts, and delete updates
after the last read on each terminal path. They cannot reveal a new
source distinction and their deletion preserves its output.

Every reachable read word has length at most $L$, its epoch at most
$N+A$, and its monotone schedule is one enumerated choice. The
unrolling preserves read counts and read lengths on each same source
and weakly decreases its update count. Its leaf fibers are exactly
the original joint path fibers. Correctness implies full row constancy
there, so Theorem 7.2 accepts it with the same terminal output.
This proves that failure of the finite enumeration excludes *every*
allowed bounded comparator. It does not require a procedure extracting
this finite unfolding from an arbitrary promised source-total program.
$\square$

**Proposition 7.4 (operational suppliers that still restrict to signed
fibers).** The all-source transformations of [JRF, Lemma 2.2, Theorem
3.1 and Lemma 3.2][JRF] restrict to (NSF.3) without change. With
$M=\max(N,5)$ and $U=M-N$, every comparator has a capped comparator
with identical output and

$$
q'(u)=q(u),\qquad a'(u)=\min(a(u),U),\qquad
\ell'(u)\le\ell(u)
\tag{NSF.17}
$$

on each same $u$. Its further caching/constant-reply cleanup has
$q''(u)\le\ell''(u)+\max(0,2-N)$ and does not increase any coordinate.

Proof. JRF's address transport is an identity on every finite native
source, including absence, with nonincreasing physical word length.
Its controller simulation preserves each successive reply and actual
early epoch. Restricting its source quantifier to $D$ changes none of
these facts. Skipped late updates and locally supplied constant or
cached replies are not actual receipts. Cleanup removes repeated
same-epoch requests and universally constant root replies, so its
argument also makes no source-language assumption. $\square$

This proposition does not import JRF's literal-history GB or its WS2S
source decision. Theorem 7.3 uses the new finite native feasibility
supplier at fixed words. Its finite enumeration already suffices
without capping; capping is useful for reducing its epoch choices.

## 8. What can be optimized without an unbounded-word decision

**Theorem 8.1 (finite-box rational weighted minimax).** In any supplied
finite box (NSF.16), one can decide feasibility and, when feasible,
compute and attain the minimum of $W_\lambda$ among all its permitted
services for every $\lambda\in\mathbb Q_{\ge0}^3$, including zero
coordinates. One can also compute the minimal feasible worst-budget
vectors within that box and an attaining service for each.

Proof. For each successful tree in the finite enumeration of Theorem
7.3 compute (NSF.15). Take the smallest weighted value, and separately
the coordinatewise minimal exact worst vectors. The comparator
unrolling in that theorem weakly decreases costs on each same source;
hence it cannot increase a nonnegative weighted sum before its
supremum. Conversely every enumerated successful tree is itself an
allowed service with the computed costs. These two comparisons prove
the weighted equality of minima and attainment.

For worst vectors every feasible comparator is weakly dominated by
one of these trees. A minimal feasible upper vector cannot strictly
exceed the exact worst vector of its attaining tree, since that
smaller vector would also be feasible. Thus the reported minimal
vectors are exact. This assertion is confined to the supplied box.
$\square$

**Corollary 8.2 (unrestricted positive weights given a successful finite
budget).** Suppose a successful finite consumer and finite upper
budget $b_0=(K_0,A_0,L_0)$ are supplied, or a supplied budget is proved
feasible by Theorem 7.3. For $\lambda_q,\lambda_a,\lambda_\ell>0$,
the unrestricted infimum over all services of Definition 1.3 is
effectively computable and attained by a finite lawful service.

Proof. Put $T=\lambda\cdot b_0$ and

$$
B_i=\left\lfloor T/\lambda_i\right\rfloor,
\qquad i\in\{q,a,\ell\}.
\tag{NSF.18}
$$

The supplied consumer has $W_\lambda\le T$ and lies in this finite
box. Any competitor with $W_\lambda\le T$ also lies in it, since
each of its sourcewise coordinates is nonnegative and bounded by
$T/\lambda_i$. A competitor with greater value cannot improve the
supplied upper value. Theorem 8.1 on $(B_q,B_a,B_\ell)$ therefore
computes the unrestricted optimum. This reasoning neither extracts a
bound from arbitrary program code nor decides whether a successful
finite budget exists in the first place. $\square$

If a weight is zero, division in (NSF.18) gives no bound on that
coordinate. The finite-box theorem still holds, but this particular
unrestricted argument no longer applies. Existing covered families
have stronger zero-weight results with their own source/action
suppliers. Some degenerate objectives are immediate, such as all
weights zero; there is no claim that every individual zero-weight
case is unresolved.

Even with a supplied successful budget, finite-box membership and
Dickson's finiteness of minimal elements do not give the complete
unrestricted effective Pareto basis. Tradeoffs outside the supplied
box can have smaller coordinates and arbitrarily larger address
budgets. JRF's general optimization scheme needs its additional
decision of feasibility for bounded reads and updates with
*unbounded* word lengths. Theorem 4.3 quantifies native trees, not
physical words, and has not supplied that decision.

## 9. Effective recovery on entire forward-closed fibers

**Definition 9.1 (closure and the auxiliary reached set).** A nonempty
fiber is forward-closed when $\rho(D)\subseteq D$. For a finite
prefix-free $Q$ let

$$
D_Q=\{u\in D:Q\subseteq\operatorname{Pos}(u)\}.
\tag{NSF.19}
$$

A complete finite binary cut means every infinite $L/R$ ray has a
prefix in $Q$, equivalently $Q$ is the leaf set of a finite full
binary prefix trie. The root singleton is complete; the empty cut is
not. The set $D_Q$ is an auxiliary quantified domain, not a stronger
entry promise and not a replacement for $D$.

**Lemma 9.2 (common deep prefixes and persistent reached subtrees).**
For every $h$ and every $u$, all replies of $\rho^n u$ at depth at
most $h$ are branch if $n\ge2(h+1)$. Once an original position is
reached, its subtree under later updates is the iterate of that same
subtree. Its whole-subtree equality with another reached position is
preserved and reflected by those updates. The trees
$\rho^n u$ are pairwise distinct as $n$ varies.

Proof. The common-prefix assertion is the branch-saturation property
used in [CAR][CAR] and [JRF, (2.4)][JRF]: each two updates increases
the minimum leaf depth by at least one, since both $\rho^2\alpha$
and $\rho^2\beta$ have branch roots. Induction gives the asserted
uniform bound. Pair preservation gives the reached-subtree identity
by induction on the original address. Injectivity of $\rho$ gives
both directions of each equality. Finally in ABC coordinates the
least primitive rank of $B(\rho^n u)$ is that of $B(u)$ plus $n$,
so these trees are distinct. $\square$

**Theorem 9.3 (forward-closed whole-fiber criterion).** For every
nonempty forward-closed $D$ of Assumption 1.2 and finite prefix-free
$Q$, the following are equivalent:

1. There is a uniform finite-read legal serial full-$R_Q$ service on $D$.
2. There is such a static service at the supplied entry epoch.
3. $Q$ is complete and its equality partition is constant on $D_Q$.

The criterion is effective on ARH inputs. It tests the whole fiber,
including sources with originally absent cuts and transient concrete
leaves. Negative instances have effectively obtainable finite
same-fiber bad pairs at every supplied original prefix depth.

Proof. Lemma 9.2 and closure show $D_Q\ne\varnothing$: advance any
source far enough to reach every member of $Q$.

Suppose first that $Q$ is incomplete. Its finite trie has an uncut
cone: there is a finite word $p$ incomparable with every member of
$Q$. This includes $p=\varepsilon$ when $Q$ is empty. From any
$u_0\in D$, advance until $p$ is reached. At all later epochs its
entire subtree remains concrete outside the cut, and consecutive
iterates there are distinct by Lemma 9.2. For any requested $h$ take
two sufficiently late consecutive iterates of $u_0$. They belong to
$D$, have the same all-branch prefix through $h$, and have different
concrete $Q$ exteriors at $p$. ARH's serial/static/prefix equivalence
therefore excludes bounded recovery.

Now suppose $Q$ is complete but two sources in $D_Q$ have different
partitions. Shift both by a common sufficiently large $n$. They stay
in $D_Q$, their respective partition bits are preserved and reflected,
and their original prefixes through any requested $h$ become equal
by Lemma 9.2. Their rows still differ. The same existence bridge
again excludes a bounded service. These arguments prove necessity
without a source-size or runtime cutoff.

Conversely assume completeness and let $\pi_*$ be the common
partition on $D_Q$. For any original $u\in D$, advance it
mathematically to some $\rho^n u\in D_Q$. For every two cuts originally
reached in $u$, their comparison is preserved and reflected; hence
their original equality bit is exactly the restriction of $\pi_*$.
This argument does not equate the original reached set with the
later one.

The finite complete trie lets a decoder traverse original nodes only
until it reaches a cut or an earlier original leaf. Its branch
decisions determine precisely the original reached set and the
entire concrete exterior. Completeness ensures that no uncut
subtree remains beyond that finite traversal. Combine this exterior
with the restriction of $\pi_*$ to its actually reached holes.
The result is the whole original row on *every* $u\in D$.

At entry $N$, each visited node $p$ is known originally reached,
from the decoded branch of its parent, with the root reached
unconditionally. Use the known-reached root case of [SLH, Theorem
2.2][SLH] on its transported subtree: one actual read at
$pR^{\lceil N/2\rceil}$ recovers whether its original root is
$\alpha,\beta$ or branch, with the theorem's parity table. The full
prefix $p$ is submitted at the physical original root. There is no
reroot action and no separate existence oracle. Do not read a cut
node, since it is a hole; do not descend below an original leaf.
This is a finite static source-total consumer. Static inclusion
gives the remaining implication.

For effectivity, Lemma 5.1 decides a counterexample to closure,

$$
\exists u\quad D(u)\land\neg D(\rho u).
\tag{NSF.20}
$$

The fixed native transform $\rho u$ is substituted into *all* old
row and history tests. Boolean complements retain the missing-guard
alternatives; they are not sign flips. Completeness of $Q$ is a finite
trie test. On a complete cut, query for two members of $D_Q$ with
opposite truth values for each of its finitely many equality bits,
using Theorem 5.2. A bit is nonconstant precisely when both truth
values occur; equivalently ask the two-source disagreement directly.
A witness in $D_Q$ gives $\pi_*$ when all bits are constant.

For a negative incomplete cut, Theorem 5.2 supplies $u_0$, the trie
supplies $p$, and finite iteration supplies the bad pairs above.
For a variable partition, the two-source feasibility query supplies
the initial disagreeing pair, then finite iteration supplies the
requested common prefix. This proves the claimed negative outputs
as well as termination of the criterion. $\square$

**Corollary 9.4 (a lawful upper price including transient exteriors).**
In Theorem 9.3's positive case let $I_Q$ be the strict ancestors of
the complete cut. The described decoder has

$$
q\le |I_Q|=|Q|-1,\qquad a=0,\qquad
\ell\le\sum_{p\in I_Q}(|p|+\lceil N/2\rceil).
\tag{NSF.21}
$$

For $Q=\{\varepsilon\}$ these costs are zero. These are upper bounds,
not general optima.

Proof. Each actual visited strict ancestor uses one current read.
There is at most one visit per trie node, and early original leaves
stop their branches. A finite full binary tree has one fewer
internal nodes than leaves. The physical words just exhibited have
the displayed lengths. $\square$

The auxiliary mathematical iteration in the necessity and partition
arguments is not performed by this static service and creates no
post-entry receipts. A source in $D\setminus D_Q$ can have a different
row from every source in $D_Q$ because its missing holes leave
concrete leaves. The decoder expressly reconstructs that difference.

## 10. Observable invariant charts with a fixed concrete outside

**Definition 10.1 (finite exact constructor-chart certificate).**
A certificate for the same $D,Q$ consists of finitely many charts
indexed by $i$, with the following data and requirements.

Each $W_i(x_1,\ldots,x_{m_i})$ is a finite *original* constructor term
over $\alpha,\beta$, pairing and the displayed residual variables.
It contains no iterate operation. Each residual variable occurs at
least once, at known original positions. Repetitions are allowed.
Its whole domain is
$V_i=\{\mathbf x\in\mathcal T^{m_i}:\Phi_i(\mathbf x)\}$, with $\Phi_i$
a finite native Boolean formula, or a formula in the fixed-observation
extension of Lemma 5.1. There are no hidden existential coordinates.
Filling is injective, since each coordinate is recovered at any one
of its original occurrences. Put $D_i=W_i[V_i]$.

The requirements are:

- Exact whole-source cover: $D=\bigcup_iD_i$, with each $D_i\subseteq D$.
  Thus every old constraint is retained on each entire chart domain.
- A supplied finite original prefix depth $s$ and finite selector
  table $\sigma$ such that every $u\in D$ lies in the selected
  $D_{\sigma(\operatorname{pref}_s u)}$. Overlap is allowed.
- Forward invariance under the *simultaneous residual action*:
  $\mathbf x\in V_i\Longrightarrow\rho\mathbf x\in V_i$.
  Constants and constructors in $W_i$ stay fixed.
- A fixed reached target set $J_i$ on each nonempty chart.
- For all $q,r\in J_i$ the target bit is preserved and reflected:
  writing $E_{i,q,r}(\mathbf x)$ for
  $W_i[\mathbf x]|_q=W_i[\mathbf x]|_r$,

$$
\Phi_i(\mathbf x)\Longrightarrow
\bigl(E_{i,q,r}(\mathbf x)\Longleftrightarrow
      E_{i,q,r}(\rho\mathbf x)\bigr).
\tag{NSF.22}
$$

This action is a mathematical operation on chart coordinates. It need
not be global $\rho$ on the whole source. Nor is it a permitted service
action: an observer still has only Definition 1.3's physical interface.
In particular a fixed $\alpha$ in $W_i$ does not turn into $\beta$
under the chart action. Empty and zero-coordinate charts are allowed.

**Lemma 10.2 (common prefixes and uncovered residual cones).** Fix a
nonempty chart satisfying residual invariance and fixed target
geometry. For any two $\mathbf x,\mathbf y\in V_i$ and supplied $h$,
the original trees $W_i[\rho^n\mathbf x]$ and
$W_i[\rho^n\mathbf y]$ have the same prefix through $h$ for sufficiently
large $n$, with an effective bound.

For a residual occurrence at position $p$ that has no prefix in $Q$,
let $Q_p=\{r:pr\in Q\}$. Exactly one of the following geometric
situations holds:

1. Some such $Q_p$ is incomplete. Then every invariant orbit of a
   chart valuation has infinitely many complete target rows and gives
   finite row-disagreeing pairs with arbitrarily long common prefixes.
2. Every such $Q_p$ is complete. Then the entire concrete target
   exterior is constant on this chart.

Proof. Before a path enters a residual occurrence it traverses the
same fixed constructor term on both sides. A fixed concrete leaf
gives the same reply, including absence below it. After entering a
residual it sees corresponding $\rho^n$ images. Lemma 9.2, for example
with $n\ge2(h+1)$, makes their remaining prefixes common. This proves
the first statement, without advancing the fixed exterior.

In situation 1 choose a suffix $r$ incomparable with every member of
$Q_p$. The original cone $pr$ has no target-cut ancestor or descendant.
Advance the residual coordinates until $r$ is reached in the coordinate
at $p$. Its further whole subtrees there are successive $\rho$ images,
hence distinct by Lemma 9.2. They remain concrete outside every target
hole. Arbitrarily late consecutive chart iterates therefore have
different rows and the same prefix through any requested $h$.
Residual invariance keeps both valuations in $V_i$.

In situation 2 consider each residual occurrence not already swallowed
by a target hole. The cut $Q_p$ is finite complete. Every member of
$Q_p$ is eventually reached along every residual orbit, by Lemma 9.2.
Fixed geometry therefore says that all are already reached for *every*
valuation in $V_i$. All their strict ancestors inside this residual
are branches, so its portion of the exterior is exactly that fixed
complete trie with holes. The other exterior pieces are fixed
constructors and concrete leaves of $W_i$. Substituting these fixed
pieces gives one entire exterior, independent of the valuation.
Repeated occurrences of a coordinate introduce no extra freedom.
These two cases exhaust the finitely many residual occurrences.
With no residual coordinates only the second case remains. $\square$

**Theorem 10.3 (whole-row constancy on observable invariant charts).**
For a certificate of Definition 10.1, bounded full-original-row recovery
on $D$ is equivalent to constancy of $R_Q$ on every nonempty $D_i$.
The criterion is effective. A positive decision constructs a lawful
finite static paid service on the whole $D$, and a negative decision
provides finite same-fiber counterexamples at every requested prefix
depth.

Proof. Suppose a bounded service exists. It restricts to each entire
$D_i$, and ARH's prefix criterion gives a finite original determining
depth on that chart. Situation 1 of Lemma 10.2 would contradict it.
In situation 2 the reached set and full exterior are fixed. If two
chart rows differ, a partition bit differs. Equation (NSF.22)
preserves and reflects each of those two truth values under every
simultaneous residual iterate. The first part of Lemma 10.2 makes
the original prefixes agree arbitrarily deeply while their rows
remain different. That too contradicts a determining depth.
Thus every nonempty chart has one whole row.

Conversely, acquire the supplied original prefix through $s$ with
SLH's actual historical decoder, evaluate $\sigma$, and output the
constant row of the selected chart. The selector guarantees actual
membership in that chart, and its row is correct on its *whole*
domain. If a source belongs to several constant charts, their output
rows agree on that source. There is no need to learn its residual
values or test a semantic chart condition. The selector uses finitely
many actual current reads, followed by a genuine halt; it is
source-total. Bounds (NSF.12) with $h=s$ are sufficient.

For effectivity, the verification and row tests are precisely the
finite native queries established in Proposition 10.4 below.
A nonconstant nonempty chart supplies two native witnesses. If its
geometry has an uncut residual cone, one witness and successive
chart iterates give the negative pairs of Lemma 10.2. Otherwise
their different row must contain a different partition bit, and
(NSF.22) and common prefixes give the negative pairs by simultaneous
iteration of both witnesses. Constructor filling puts each pair back
in the entire original $D$. $\square$

**Proposition 10.4 (effective certificate verification).** All the
requirements of Definition 10.1, and its whole-chart row-constancy
tests, reduce effectively to the existential decision of Theorem 4.3
via Lemma 5.1. The certificate's selector depth and chart templates
are supplied finite data. The proposition does not search for a
certificate for every arbitrary fiber.

Proof. Membership of a source $u$ in $D_i$ is a finite deterministic
pattern-matching predicate. Match the fixed constructor term $W_i$,
its concrete leaves and its repeated coordinate occurrences. At a
representative occurrence $p_j$ recover the mathematical whole subtree
$u|_{p_j}$ and substitute it into $\Phi_i$. Every other occurrence
of that variable must be reached and equal to the representative.
When all tests hold, filling those recovered values reconstructs $u$,
and those values belong to $V_i$. Conversely every chart filling
passes them. This proves both source directions of membership.
Absence at a required occurrence makes matching fail; it is not an
extra value for the coordinate.

These matching predicates, and their complements, compile by Lemma
5.1's deterministic prefix cases. First split the source beyond all
representative occurrence positions. Each recovered coordinate is
then a native expression in that case's residual variables.
Substitute those expressions into $\Phi_i$ and perform any further
finite prefix splitting demanded by its fixed observations. The
finite supplied expressions and fixed navigation depths make this
a finite composition of the compiler. Therefore a counterexample to either
inclusion in $D=\bigcup_iD_i$ is an existential finite-observation
query on one source, including every original retained constraint.
No arbitrary negation of an existential projection is used; the
original occurrence inverses provide the actual coordinate terms.
Empty chart domains are tested by $\exists\mathbf x\,\Phi_i$.

Invariance fails exactly when

$$
\exists\mathbf x\quad
\Phi_i(\mathbf x)\land\neg\Phi_i(\rho\mathbf x).
\tag{NSF.23}
$$

Geometry differs from the asserted finite $J_i$ by one fixed reached
test. Preservation or reflection of a bit fails by the exclusive-or
of the two guarded comparisons in (NSF.22), with $\Phi_i$ retained.
All are queries of Lemma 5.1. One witness may be used to compute $J_i$
and then verify it; an empty chart needs no such geometry.

For the selector, there are finitely many depth-$s$ prefix patterns.
For each pattern with table value $i$, test for a source in $D$ with
that prefix and outside $D_i$. Their absence is precisely selector
correctness. An invalid index on a nonempty pattern is rejected.
No semantic chart label is added to the input.

Finally row nonconstancy is

$$
\exists\mathbf x,\mathbf y\quad
\Phi_i(\mathbf x)\land\Phi_i(\mathbf y)\land
R_Q(W_i[\mathbf x])\ne R_Q(W_i[\mathbf y]).
\tag{NSF.24}
$$

It is an existential native observation query and keeps all fields of
the row. Its failure on a nonempty chart allows a returned source
witness to label that chart's output. The construction is finite and
each positive or negative subquery terminates. $\square$

The chart criterion allows fixed concrete outside pieces, unequal
residual-coordinate depths, repeated coordinates and arbitrary
non-atomic residual trees. Global forward closure is not required.
The finiteness and observable selection of the cover, and invariance
of each *whole* domain, are hypotheses with effective checks; they
are not assumed consequences of a finite normal-form decomposition.

## 11. Inhabited boundaries and native counterexamples

**Example 11.1 (native algebra versus ambient syntax).** The formula

$$
\rho x=\langle x,\alpha\rangle
\tag{NSF.25}
$$

is satisfiable at $x=\beta$. The formula $\rho x=\alpha$ is
unsatisfiable, since every translated normal rank is at least one.
Also $F([1],[0])\ne[2]$ is an ambient inequality between two codes
whose expansions are the same native tree. The former code is
nonnormal. These three facts respectively falsify a native
free-constructor interpretation, an unrestricted inverse shift, and a reduction that
forgets normality.

The fixed-shape rank constraints in Theorem 4.3 retain unforced
non-atomic solutions as well. For example
$x=\langle\alpha,\alpha\rangle$ and
$y=\langle\beta,\beta\rangle$ satisfy $\rho x=y$; neither is atomic,
since their codes are $F([0],[0])$ and $F([1],[1])$. This observation
illustrates its domain, not a new resource result for the graph family
already covered by [GRS][GRS].

**Example 11.2 (a forward-closed whole signed fiber with transient
leaves).** Take a root old cut, its unique one-hole row, no literal
records, and the actually acquired negative record
$(2,L,2,R,\ne)$. Its entire source fiber is

$$
D=\{\alpha,\beta\}\ \cup\
  \{\langle x,y\rangle:x\ne y\}.
\tag{NSF.26}
$$

Indeed $\rho^2\alpha=T_2$ has distinct children $\beta,\alpha$,
and $\rho^2\beta=T_3$ has distinct children $T_2,\beta$.
Both endpoints are reached. For an original pair the children are
$\rho^2x,\rho^2y$, distinct exactly when $x\ne y$ by injectivity.
This proves both inclusions, including the guards. The fiber is
nonempty, includes arbitrary non-atomic residuals, and is
forward-closed: the two leaves progress into $\beta$ and an
unequal-child pair, and original unequal children stay unequal.

For $Q=\{L,R\}$, the auxiliary $D_Q$ consists of the pairs and has
the constant two-class partition. Theorem 9.3 recovers the original
row with one current read at $R^{\lceil N/2\rceil}$, $N\ge2$,
decoding the original root as $\alpha,\beta$ or branch. These are
three different full rows: two concrete leaf rows with no holes,
and the two-hole unequal row. A zero-read controller cannot output
all three from one common input, so the raw upper bound one is
attained as an optimum here. This lower bound concerns raw reads,
not a minimum literal length.

Replacing the entry domain by $D_Q$ would lose the two concrete
outputs. For $Q=\varnothing$, the same inhabited closed fiber has
no bounded whole-tree service, by incompleteness of that cut.

**Example 11.3 (a selected chart cover without global closure).**
Take $P=\{L,R\}$, the pair exterior with two distinct old classes,
literal record $(0,L,\alpha)$, and signed record
$(2,RL,2,RR,\ne)$. The entire fiber is

$$
D=
\{\langle\alpha,\beta\rangle\}
\ \cup\
\{\langle\alpha,\langle x,y\rangle\rangle:x\ne y\}.
\tag{NSF.27}
$$

To verify it, write the old source as $\langle z,w\rangle$ with
$z\ne w$. The literal forces $z=\alpha$. Apply the exact calculation
of Example 11.2 to $w$: the signed record permits $\alpha,\beta$
or an unequal-child pair. The old disequality removes $w=\alpha$
and removes nothing else. Conversely every source displayed in
(NSF.27) satisfies every old and new constraint and both guards.

For $Q=\{RL,RR\}$ use one ground chart
$W_0=\langle\alpha,\beta\rangle$ and one constructor chart
$W_1(x,y)=\langle\alpha,\langle x,y\rangle\rangle$ with domain
$x\ne y$. The latter domain is invariant under simultaneous $\rho$;
its target children remain distinct. Its reached set is both cuts,
whereas the ground chart has neither reached. Each chart has a
constant whole row. The original root reply at the known-reached
address $R$ selects the chart: $\beta$ selects the first, branch the
second. One actual read at $RR^{\lceil N/2\rceil}$ recovers that
reply at entry $N\ge2$ using the known-reached decoder.

The whole fiber is not globally forward-closed, since its fixed
original left $\alpha$ becomes $\beta$ under global $\rho$.
Thus Definition 10.1 applies beyond the global-closure premise.
The construction retains the old cross-class disequality even
though it is outside the new cut cones. The paid producer is ARH's
whole-source acquisition, and the chart selector is an actual
literal read, not an atomicity test.

**Proposition 11.4 (a finite semantic cover is not a selector).**
Let $D$ be all original pairs, represented by a root old row and
the literal record $(0,\varepsilon,\mathsf{branch})$, with
$Q=\{L,R\}$. The equal-child and unequal-child subsets are two
exact charts with invariant domains, fixed geometry, preserved and
reflected target bits, and one constant whole row each. Nevertheless
their union has no bounded full-row service and no finite original
prefix selector for this cover.

Proof. Use $W(x,y)=\langle x,y\rangle$ in both charts, with domains
$x=y$ and $x\ne y$. These properties follow from injectivity of
$\rho$. For every $h$ choose $m\ge2(h+1)$ and compare

$$
u_m=\langle T_m,T_m\rangle,\qquad
v_m=\langle T_m,T_{m+1}\rangle .
\tag{NSF.28}
$$

Both lie in the exact same entry fiber, agree through depth $h$,
and have different full partitions. The two chart domains are
disjoint. Any correct selector must therefore distinguish these
sources, which a common finite prefix cannot do. ARH's existence
bridge excludes bounded recovery. A finite row image, inhabited
charts and decidable chart membership on concrete trees do not
provide the missing observable selector. $\square$

**Example 11.5 (the chart hypotheses cannot be suppressed).**
The following inhabited native fibers distinguish the other premises.

First, use the root old row and the literal record
$(0,L,\mathsf{absent})$. Its entire fiber is $\{\alpha,\beta\}$.
With $Q=\varnothing$ one known-root historical read recovers the
whole source, although its row is not constant. The one-chart
presentation $W(x)=x$ has no forward-invariant domain. Its geometry
and partition conditions are vacuous; without invariance the
necessity in Theorem 10.3 would be false.

Second, (NSF.26) with the single chart $W(x)=x$ has an invariant
domain, but for $Q=\{L,R\}$ its reached geometry varies. Its whole
row is nonconstant and is recovered with one read. Thus fixed
geometry cannot be deleted from the chart criterion. The global
criterion instead handles these transient leaves explicitly.

Third, let the old row at $P=\{R\}$ have concrete exterior
$\langle\alpha,\square\rangle$ and no further records. Its entire
fiber is $\{\langle\alpha,x\rangle:x\in\mathcal T\}$.
Take that one chart and $Q=\{L,R\}$. Its geometry is fixed and its
residual domain invariant. The equality bit is $x=\alpha$,
which changes when $x=\alpha$ advances to $\beta$. The row is
nonconstant but is recovered by one historical known-root read
inside $R$, testing whether its original reply is $\alpha$.
Preservation and reflection (NSF.22) are therefore essential.

These examples use the whole specified acquired fibers. None
selects a favorable subfamily as a replacement source domain.

**Example 11.6 (one finite query does not settle all depths).**
The all-tree fiber, given by the root old row and empty histories,
is inhabited. For $Q=\{\varepsilon\}$ every determining-prefix
test succeeds and zero actions suffice. For $Q=\varnothing$,
every fixed $h$ test fails: $T_m,T_{m+1}$ with $m$ sufficiently
large have equal prefixes and different whole sources.
For $Q=\{L,R\}$ the pair (NSF.28) similarly refutes every depth.
The forward-closure theorem settles these particular unbounded
questions. Theorem 6.1 alone only returns a correct answer to each
individual finite test; its termination proof supplies no universal
depth bound on a different arbitrary signed fiber.

**Example 11.7 (weighted maxima must share a source).** On the exact
leaf fiber $\{\alpha,\beta\}$ from Example 11.5 at entry zero,
consider a lawful whole-source service that reads the root. On
reply $\alpha$ it performs two updates and halts with $\alpha$;
on reply $\beta$ it reads $R$ twice and halts with $\beta$.
Its sourcewise costs are respectively $(1,2,0)$ and $(3,0,2)$.
For weights $(1,1,1)$ its weighted worst value is $5$, whereas
the sum of its separate coordinate maxima is $7$. Both runs
are actual finite runs on their respective sources. Redundant
reads and terminal updates make this service nonoptimal, but
do not make it an illegal comparator. Theorem 7.3's unrolling
can delete the terminal updates; its optimum comparison uses
sourcewise dominance, not equality of these two maximum formulas.

## 12. The remaining unbounded obligations

**Open problem 12.1 (unrestricted prefix limitedness).** For arbitrary
nonempty (NSF.3) outside supplied certificates, decide

$$
\exists h\ge0\quad\operatorname{PrefDet}(D,Q,h).
\tag{NSF.29}
$$

Theorem 6.1 gives a terminating test for each supplied $h$, and
enumeration of $h$ semidecides positive instances, with actual paid
consumers. It gives no negative stopping rule on arbitrary inputs.
The witness shapes of Theorem 4.3 depend on the finite formula,
which here changes with $h$. They are not a uniform bound on the
source fiber or on the sequence of bad-pair formulas.

**Open problem 12.2 (unbounded physical words and general exact
resources).** On the same arbitrary fiber, decide bounded $(q,a)$
feasibility while physical words have no supplied length bound.
Then supply the complete unrestricted effective Pareto frontier and
the general rational weighted interface, including the zero-weight
cases not covered by a separate argument or a recognized supplier.

JRF's all-source cap already bounds useful actual update epochs.
A bounded read count gives finitely many tree *shapes*, but their
word labels still range over an infinite set. No quantifier over
such words occurs in Theorem 4.3. Running Theorem 7.3 at
$L=0,1,\ldots$ is a positive semidecision, not the requested NO
decision. Existence of a finite minimal antichain supplies no
effective discovery cutoff. Even a known successful finite consumer
does not automatically bound every possible Pareto tradeoff.

CAR, SRF, CRF and GRS already solve stronger resource questions
on their respective recognized atomic, synchronous,
constructor-elimination and fixed acquired-graph domains.
Their scoped answers are reused when the entire input meets
their premises. Arbitrary extra signed relations cannot be inserted
into their source-language encodings without a new correspondence.
No recognition failure here or in those suppliers implies
undecidability or impossibility of recovery.

The increment supplies one terminating source-feasibility producer
and its finite-query consumers. It neither changes the original
target to a finer observation nor regards a finite witness set as
the entry domain. The unrestricted continuing relation/recovery
programme is not completed by these results.

## 13. Sources, proof scope and originality limits

**References 13.1 (exact mathematical suppliers).** Repository
contracts are read at the immutable [source baseline][BASE].
The following results are reused at their displayed scope.

| Source | Exact use and boundary |
| --- | --- |
| [ABC §§2–5][ABC] | All-native $B/E$ inverses, smart pairing, translation with its image restriction, masks and full-source correspondence. No ambient uniform normality predicate is inferred. |
| [ARH §§1–3][ARH] | Entire paid signed input, both guards, original old-class reconstruction, prefix cells, paid producer and static/serial/prefix existence equivalence. Its recognized fragment decisions remain available. |
| [SLH Theorem 2.2][SLH] | Actual current decoding of old literal replies, including absent paths and the one-read known-reached root form under a full physical prefix. No past event is fabricated. |
| [JRF §§2–4][JRF] | Sourcewise nonexpansive late probes, cap, cleanup and finite comparator unrolling. Its literal-only logical decision is not applied to arbitrary signed histories. |
| [CAR][CAR] | Native atomic-cycle recognizer, exact joint atomic charts, arithmetic prefix and physical-resource results. Theorem 4.3 permits residual non-atomic shapes not forced by that recognizer. |
| [SRF][SRF] | Full synchronous-family source/action formulas and exact resources, including non-atomic residuals. No arbitrary constructor-offset closure is presumed. |
| [CRF][CRF] | Entire constructor-elimination family, finite-marker common-word bridge, exact resources and sharp native example. Its covered bridge is not proposed again here. |
| [GRS §§1–2 and resource theorems][GRS] | Fixed graph $\langle\rho y,y\rangle$ with every retained literal history and original cut; exact graph resources. Its input explicitly excludes arbitrary further signed constraints. |
| [TPO Definition 1.2 and §4][TPO] | Nondefinability in its exact term-power language. It does not exclude a formula-dependent existential witness replacement or prove general native undecidability. |

**References 13.2 (formal-source correspondence).** The native source
identification is $\alpha=\mathtt{of\ true}$,
$\beta=\mathtt{of\ false}$, pairing $\mathtt{FreeMagma.mul}$ and
$\rho=\mathtt{substitution}$. Source inspection includes public and
private/local declarations; it is not fresh kernel evidence.

| Source declaration | Supplied interface and its limit |
| --- | --- |
| [SourceTransportCentralizer, source_transport_centralizer][D5-CENTRAL] | Atomic stability classification, commuting pairing-preserving maps, injectivity and the inverse on the actual image. Its local classification, orbit and injectivity arguments are not a signed constraint solver. |
| [NativeDepthPatterns, depthEquiv, original_present_transport, original_prefix_locality][D5-DEPTH] | Exact finite-prefix decomposition and forward original-address locality. Its History is a list of numeral epoch/address/reply triples. |
| [NativeGroundSeparation, simultaneous_ground_separation][D5-GROUND] | Ordinary native term disequalities, with private count_length, evaluated_length, compound_mass_ne and bounded_eval_injective providing equal-mass separation. No interpreted $\rho$-equation solver is contained in this type. |
| [NativeCutFibers, rowFiberEquiv][D5-CUT] | Whole old-row filling with injective old-class valuations. The private recover_fill and fill_injective identify both source directions. |
| [NativeHistoryCells, cell_feasibility_exact and historyCellEquiv][D5-HISTORY] | Exact literal-history cells, all old-class disequalities and symbolic recutting. Its private syntax_iff_ground uses ordinary term separation. It does not assert arbitrary signed whole-subtree feasibility. |
| [NativeSymbolicRecutting, symbolic_recut_exact][D5-RECUT] | Reached order, concrete exterior and every equality pair when all residual variables are beyond the supplied cut depth; private termAt_fill and exterior_commute carry its structural identities. |
| [Pinned mathlib, Algebra/Free.lean][FREE] | FreeMagma's two constructors, lift, map, hom_ext and positive leaf length. Free constructors are used for shape unification only after the native collapse choices. |

The pinned mathlib revision is
db584cd6d46c92f209a44c0f1c829460d327499d.
The comparisons above do not claim exhaustive absence in every library
or compiled specialization of any new result. External-stream restart
and scanner-runtime results require their own probabilistic and runtime
hypotheses; none supplies a deterministic finite-tree constraint
decision by changing the name of its state.

**References 13.3 (bounded primary-literature comparison).**

| Primary source | Verified premise and role |
| --- | --- |
| Marshall, Meadows and Narendran, [*On Unification Modulo One-Sided Distributivity: Algorithms, Variants and Asymmetry*][MMN], arXiv:1503.06687v2, §5, especially Lemmas 5.6–5.7 and Theorem 5.8 | literature-attested: a typed single-homomorphism presentation of one-sided distributivity, with cycle failures using its subterm-collapse-free theory. The native identities $\rho\alpha=\beta$ and $\rho\beta=\langle\beta,\alpha\rangle$ are additional interpreted constant laws. Example 11.1 prevents a direct transplant of a free occurrence/cycle failure rule. |
| Barguñó, Creus, Godoy, Jacquemard and Vacher, [*Decidable Classes of Tree Automata Mixing Local and Global Constraints Modulo Flat Theories*][BCGJV], arXiv:1302.6960v2, §2.4 and Theorem 5.22 | literature-attested: emptiness of its stated automata class, with a computable minimal-run height bound. Its flat equations have equal side heights at most one and the same variable set on both sides. Native homomorphism distribution has height two, and $\rho\alpha=\beta$ has unequal side heights. No direct encoding into that theorem is claimed. |
| Kuncak and Rinard, [*On the Theory of Structural Subtyping*][KR], arXiv:cs/0408015v1, §§5–6, Figures 9–11, Theorem 90 and Corollary 91 in the PDF | literature-attested: free term-power constructors, shapes and pointwise lifted base relations in the specified language; decidability from a decidable base structure. TPO identifies the missing uniform native normal-domain interpretation in that language. The present existential proof does not invoke that interpretation. |
| Finite first-order unification, integer difference constraints and equal-mass ground separation | Standard methods, used explicitly in §§3–4 with their finite-tree, nonempty-leaf and nonleaf-marker premises. These methods are not claimed as inventions. |

The three pinned primary texts delimit the direct transfers considered
here. Failure of those transfers does not exclude every faithful
encoding into those or other decidable theories. There is no
literature-wide novelty, priority or general undecidability claim.
The formula-dependent native witness replacement in Theorem 4.3,
its whole signed-fiber applications and its effective invariant
recovery consequences are repo-derived ordinary deductions with
proofs in this volume.

**Status 13.4 (evidence boundary).** The mathematical evidence consists
of the universal ordinary proofs and the exact finite examples above,
together with the cited suppliers at their stated hypotheses.
No experiment, implemented solver or Lean build is presented as
validation of these universal claims. Structural document checks
do not verify the mathematics or authenticate physical acquisition.
The access and resource conclusions retain Assumption 1.2's actual
producer, complete-state and same-register contracts. Unbounded
limitedness and the remaining general resource questions retain
the obligations of §12.

[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[SRF]: RECURSIVE_RELATIONAL_OBSERVATION_SYNCHRONOUS_RESOURCE_FRONTIER.md
[CRF]: RECURSIVE_RELATIONAL_OBSERVATION_CONSTRUCTOR_RESOURCE_FRONTIER.md
[GRS]: RECURSIVE_RELATIONAL_OBSERVATION_GRAPH_RESOURCE_SEPARATION.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[BASE]: https://github.com/the-omega-institute/trureturing/tree/ac6649d4d23e9d97ab24c2cc0922937e31acc87c
[D5-CENTRAL]: https://github.com/the-omega-institute/trureturing/blob/ac6649d4d23e9d97ab24c2cc0922937e31acc87c/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[D5-DEPTH]: https://github.com/the-omega-institute/trureturing/blob/ac6649d4d23e9d97ab24c2cc0922937e31acc87c/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5-GROUND]: https://github.com/the-omega-institute/trureturing/blob/ac6649d4d23e9d97ab24c2cc0922937e31acc87c/D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[D5-CUT]: https://github.com/the-omega-institute/trureturing/blob/ac6649d4d23e9d97ab24c2cc0922937e31acc87c/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[D5-HISTORY]: https://github.com/the-omega-institute/trureturing/blob/ac6649d4d23e9d97ab24c2cc0922937e31acc87c/D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[D5-RECUT]: https://github.com/the-omega-institute/trureturing/blob/ac6649d4d23e9d97ab24c2cc0922937e31acc87c/D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[FREE]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Free.lean
[MMN]: https://arxiv.org/pdf/1503.06687v2
[BCGJV]: https://arxiv.org/pdf/1302.6960v2
[KR]: https://arxiv.org/pdf/cs/0408015v1

## 追加锚（本行以下为增补区）
