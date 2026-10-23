# Retained cross-record relations and unknown native epochs

This volume extends the finite signed native feasibility argument to
unknown, unbounded natural epochs. Its principal result is an effective
finite affine description of the entire chronological epoch support,
with a terminating existence decision and one finite common-source
witness at every accepted tuple. The finite templates select witnesses;
they do not parametrize every original source in a fiber.

The arguments are ordinary mathematics, not Lean kernel evidence.
The reference-input and append-only conventions of the theory-volume
template apply: incorporated statements retain their bytes and numbers;
corrections and extensions follow the final append anchor. The native
deductions below are `repo-derived`; supplied results and their exact
language boundaries are identified explicitly.

## 1. Native records, signed memory and the target relation

**Definition 1.1 (domain and observations).** Throughout,

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle u,v\rangle&=\langle\rho u,\rho v\rangle.
\end{aligned}
\tag{NCE.1}
$$

These are all nonempty finite ordered full trees, with free literal
constructors. Put $T_j=\rho^j\alpha$. An address is a finite word over
$L,R$, with root $\varepsilon$. The subtree $u|_p$ is defined only for
$p\in\operatorname{Pos}(u)$. A literal read has one of the replies
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$.

For a finite prefix-free cut $P$, the complete row $R_P(u)=(C,\pi)$
retains every exterior constructor and concrete leaf, a hole at each
reached member of $P$ labelled by its actual address, and the entire
equality partition of the hidden subtrees. Different classes assert
disequality. An unreached requested cut leaves its concrete blocking
leaf visible. These are [NUE, Definition 1.1][NUE] and the independent
record of [ActualCutPartitionDecoder][ROW], `literalRecord` and
`canonicalRow_record_iff`, with [its Scribe][ROW-S].

**Definition 1.2 (input and exact support).** An input $I$ consists of
$m\ge1$ finite proposed complete rows $(P_i,R_i)$ and a finite set
$\Lambda$ of triples $((i,p),(j,q),\epsilon)$, where
$\epsilon\in\{=,\ne\}$. Both endpoints must be addressed reached
holes in the indicated records. Class names are local to each row;
the same printed class name in different rows creates no link.

Use the proposed-row validation of [NUE, Definition 1.2 and Proposition
1.3][NUE]: the cut is prefix-free; the exterior is a finite full ordered
context; each hole occurs once at its own address in the cut; every
other requested cut is blocked by a concrete leaf at a strict prefix;
and the partition is an equivalence relation on exactly the holes.
Also validate the address alphabet, record indices and link signs, and
require both link endpoints to be holes. Malformed input is rejected.
For representation purposes its formula is $\mathsf{false}$, while the
diagnostic distinguishes malformed input from valid but inconsistent
input. In particular neither sign is a test on a default absent tree.

For valid input let $\mathscr H_I$ be the set of pairs $(t,\mathbf n)$
with $t\in\mathcal T$, $\mathbf n\in\mathbb N^m$,

$$
\begin{gathered}
\operatorname{Chron}(\mathbf n):\quad
0=n_0\le n_1\le\cdots\le n_{m-1},\\
R_{P_i}(\rho^{n_i}t)=R_i\quad(i<m),\\
(\rho^{n_i}t)|_p\ \epsilon\ (\rho^{n_j}t)|_q
\quad(((i,p),(j,q),\epsilon)\in\Lambda).
\end{gathered}
\tag{NCE.2}
$$

The last line includes both reachedness guards. Define
$E_I=\{\mathbf n:\exists t\ (t,\mathbf n)\in\mathscr H_I\}$;
this is the requested $E_\Lambda$. There is no inhabitation premise,
no supplied finite epoch set, and no source size, depth or age bound.
Ties, $m=1$, empty cuts, root cuts, blocked and mixed cuts, rows without
holes, and empty $\Lambda$ are included.

**Definition 1.3 (supplier boundary).** [NSF, Definition 1.1, Lemma
5.1 and Theorem 5.2][NSF] already decide finite signed comparisons,
including cross-record comparisons, at supplied numeral epochs. Their
grammar expressly excludes quantified epochs. [ABC, Theorems 2.2--2.3][ABC]
provide the faithful normal coordinates and the translation identity
used below. [NUE, Theorems 2.2 and 3.3][NUE] give a source-preserving
row-only cap, while its Proposition 6.3 already refutes extending that
cap to cross-epoch comparisons. None of these results is restated as
new signed fixed-epoch feasibility.

[NIC, Definition 1.2][NIC] permits variable atomic ages $T_{n_j+c}$,
but its arbitrary residuals have fixed powers $\rho^a(z_i)$.
[NIS, Section 11][NIS] expressly excludes quantified $\rho^pZ$ from
its stated grammar. The new bridge here is the parameter-independent
shape construction, its pointwise witness replacement, and elimination
of symbolic affine rank differences. Those steps are proved rather
than added to a supplier's interface by notation.

## 2. Exact common-source compilation

**Definition 2.1 (shared class variables).** Write $R_i=(C_i,\pi_i)$,
let $H_i$ be its addressed holes, and let $\mathcal B_i=H_i/\pi_i$.
Introduce a native variable $x_{i,b}$ for each $b\in\mathcal B_i$,
reusing it at every occurrence of that class. Variables in different
rows remain distinct names until constrained. Set

$$
\begin{aligned}
W_i(\mathbf x)&=C_i[(x_{i,[p]})_{p\in H_i}],\\
\Delta_i(\mathbf x)&=\bigwedge_{b\ne c\in\mathcal B_i}
                    x_{i,b}\ne x_{i,c},\\
L_I(\mathbf x)&=\bigwedge_{((i,p),(j,q),\epsilon)\in\Lambda}
                    x_{i,[p]}\ \epsilon\ x_{j,[q]}.
\end{aligned}
\tag{NCE.3}
$$

Empty products have their unique empty valuation and empty conjunctions
mean true. With one further variable $t$, define

$$
\Psi_I(\mathbf n,t,\mathbf x)=
 \bigwedge_{i<m}\bigl(\rho^{n_i}t=W_i(\mathbf x)
                         \ \land\ \Delta_i(\mathbf x)\bigr)
 \ \land\ L_I(\mathbf x).
\tag{NCE.4}
$$

**Proposition 2.2 (exact application of proposed-row filling).** For
every valid $I$, every $t\in\mathcal T$ and every chronological
$\mathbf n$,

$$
(t,\mathbf n)\in\mathscr H_I
\quad\Longleftrightarrow\quad
\exists\mathbf x\in\prod_i\mathcal T^{\mathcal B_i}
                     \ \Psi_I(\mathbf n,t,\mathbf x).
\tag{NCE.5}
$$

When this holds, the class valuation is unique for this $t,\mathbf n$.
Thus this stage preserves every original source, before any witness
replacement takes place.

Proof. Apply [NUE, Proposition 1.3][NUE] to $u=\rho^{n_i}t$ for each
$i$. Its filling equivalence retains the entire exterior, the concrete
strict-prefix blockers, and every different-class inequality. Its
inverse reads the subtree at a representative hole of each class.
These inverses give the unique $\mathbf x$ on the right of (NCE.5).
Every declared link is then exactly its comparison in $L_I$.

Conversely, filling the validated $C_i$ cannot change a displayed
exterior node or blocker. Prefix-freeness ensures that filling one
hole cannot conceal a different requested cut. Shared class variables
and $\Delta_i$ give precisely the full partition. The equation
$\rho^{n_i}t=W_i$ therefore identifies this row with the actual iterate
of the same $t$ used in all other equations. Both endpoints of every
link are reached in these filled rows, so its sign is a comparison of
their actual values. This proves the converse and uniqueness.

The filling supplier is grounded in [NativeCutFibers][CUT],
`rowFiberEquiv`, whose `LegalValues` are injective on the entire set
of appearing classes; see [its Scribe][CUT-S]. No product of separate
record-source fibers is substituted for (NCE.4). A later-born address
is handled by its entire iterate equation, without backward transport
through an originally absent subtree. $\square$

## 3. A symbolic difference calculation

**Definition 3.1 (affine rank system).** Let $\mathbf z\in\mathbb N^k$
be parameters. An affine form has integer coefficients and constant
term. A rank system has finitely many unknowns $r_v\in\mathbb N$,
one distinguished vertex $o$ with $r_o=0$, and constraints

$$
r_u-r_v=a_e(\mathbf z),\qquad
r_u-r_v\ne b_e(\mathbf z).
\tag{NCE.6}
$$

Fixed-rank requirements are edges to $o$. An isolated $o$ is allowed.
Choose a spanning forest of the undirected equality graph, retaining
edge orientations as signs. Root the component containing $o$ at $o$.
Root each other component arbitrarily. Summing signed edge labels along
tree paths gives affine potentials $\delta_v(\mathbf z)$, with each
root potential zero and with each forest edge satisfying
$\delta_u-\delta_v=a_e$ identically.

**Lemma 3.2 (uniform elimination of all scalar ranks).** The parameter
support of (NCE.6) is exactly the following finite conjunction
$Q(\mathbf z)$:

$$
\begin{array}{ll}
\delta_u-\delta_v=a_e&\text{for every equality edge},\\
\delta_v\ge0&\text{for every vertex in the component of }o,\\
\delta_u-\delta_v\ne b_e&\text{for every disequality inside one
 equality component}.
\end{array}
\tag{NCE.7}
$$

All potentials and conditions are constructed before any parameter
assignment. For an accepted assignment one can construct all ranks by
a finite arithmetic procedure. If $D$ is the total number of disequalities
and $K=\max_v|\delta_v(\mathbf z)|$, the construction can choose
$0\le r_v\le2K+D$ for every vertex.

Proof. Fix an arbitrary parameter assignment. Following the forest
edges in any solution gives $r_v=B_C+\delta_v$ in each component $C$.
The anchored component has $B_C=0$. Every remaining equality yields
the first line of (NCE.7), natural ranks in the anchored component
give the second, and same-component disequalities give the third.
Thus all three lines are necessary, including evaluated cycle sums.

For sufficiency first assign $r_v=\delta_v$ in the anchored component.
For each other component, in any fixed order, put

$$
L_C=\max\bigl(\{0\}\cup\{-\delta_v:v\in C\}\bigr).
\tag{NCE.8}
$$

Each disequality to a previously assigned component excludes at most
one value of $B_C$. There are at most $D$ such values. Choose the
first permissible integer among $L_C,L_C+1,\ldots,L_C+D$ and set
$r_v=B_C+\delta_v$ in this component. Its ranks are nonnegative.
Its equalities and internal disequalities hold by (NCE.7); its
disequalities to earlier components hold by the choice. Every
cross-component disequality is handled when its later component is
assigned. This constructs a solution after finitely many choices.
Since $L_C\le K$, every free rank is at most $2K+D$; the anchored
ranks are at most $K$. The argument applies to every assignment of
$\mathbf z$ with the same forest and the same formula. In particular,
a symbolic cycle label such as $z_1-z_2$ is retained as the condition
$z_1-z_2=0$, not rejected for being a nonzero polynomial. $\square$

**Lemma 3.3 (parameter-uniform whole-block replacement).** Suppose
the vertices instead denote natural-valued functions $U_v$ on the
leaves of a common nonempty finite shape, with equations and
disequalities $U_u=U_v+a_e(\mathbf z)$ and
$U_u\ne U_v+b_e(\mathbf z)$. There are no fixed-function constraints
and no comparisons with individual leaf values. At every parameter
assignment, existence of such functions on some nonempty finite shape
is equivalent to existence of constant functions on any prescribed
nonempty finite shape. The constant values can be obtained by the
unanchored part of Lemma 3.2.

Proof. In a component the forest equations give
$U_v=B_C+\delta_v$ pointwise. A cycle with nonzero evaluated sum is
impossible, because there is at least one leaf at which to evaluate it.
An internal disequality is false exactly when its offset is forced
zero, and otherwise holds at every leaf. These are the unanchored
conditions in (NCE.7). For different components, choosing constant
bases makes each disequality forbid just one difference of their
bases; the finite-avoidance construction in (NCE.8) satisfies them
all and keeps every rank natural. Constant functions give the reverse
implication immediately. The chosen constants may depend on the
parameter assignment; the prescribed replacement shape does not.

This is the symbolic-offset extension of [NSF, Lemma 4.2][NSF].
It is about whole-function inequality, the negation of equality. It
does not replace arbitrary pointwise predicates, selected positions
inside an unspecified block, or universal properties of that block.
$\square$

## 4. Uniform elimination of existential native trees

**Definition 4.1 (the admitted parameter language).** Let $\mathbf z$
be a finite tuple of free natural parameters. The finite expression
grammar is

$$
A::=\alpha\mid\beta\mid x_j\mid\langle A,A\rangle
                  \mid\rho^{a(\mathbf z)}(A),
\tag{NCE.9}
$$

where each $a$ is a specified integer-affine form. A specified finite
Boolean combination $G(\mathbf z)$ of affine equalities, disequalities
and weak inequalities includes, as conjuncts, $a(\mathbf z)\ge0$ for
every exponent occurrence.
Only assignments satisfying $G$ interpret the expressions. Fixed
natural powers and the powers $\rho^{z_i}$ are special cases; nesting
and repeated parameters are allowed. Fixed finite ground trees are
abbreviations in this grammar. Let $\Phi(\mathbf z,\mathbf x)$ be a
finite Boolean combination of equalities between these expressions.
Every tree variable is existential over $\mathcal T$. There are no
free unknown tree parameters, tree quantifier alternations, variable
addresses, arbitrary morphisms or products of epoch variables.

**Theorem 4.2 (finite affine support and simultaneous finite witnesses).**
From $G,\Phi$ one can effectively construct a finite set $\mathcal A$
and finite conjunctions $Q_b(\mathbf z)$ of affine equalities,
disequalities and weak inequalities such that, for every
$\mathbf z\in\mathbb N^k$,

$$
G(\mathbf z)\ \land\
\exists\mathbf x\in\mathcal T^r\ \Phi(\mathbf z,\mathbf x)
\quad\Longleftrightarrow\quad
G(\mathbf z)\ \land\ \bigvee_{b\in\mathcal A}Q_b(\mathbf z).
\tag{NCE.10}
$$

The construction also returns finite normal-code templates for every
tree variable and, for each true branch, a terminating assignment of
their ranks at that same $\mathbf z$. Expanding the templates gives one
simultaneous tuple of finite native witnesses. The finite branch list
and all template shapes are independent of the values of $\mathbf z$.

Proof. The proof extends [NSF, Sections 2--4][NSF]. The extension must
preserve the free parameter tuple at each step; the details below
establish that quantifier order.

First use [ABC, Theorems 2.2--2.3][ABC]. Its normal codes are finite
terms built from $[j]$ for $j\in\mathbb N$ and $F$, excluding every
primitive cherry $F([j+1],[j])$. The maps $B,E$ are inverse between
$\mathcal T$ and this normal domain $\mathcal N$. Native pairing is
the smart constructor

$$
J(X,Y)=
\begin{cases}
[j+2],&X=[j+1],\ Y=[j],\\
F(X,Y),&\text{otherwise},
\end{cases}
\qquad B(\rho^n t)=\tau_nB(t),
\tag{NCE.11}
$$

where $\tau_n$ adds $n$ to every primitive rank. These supplied
identities hold for every natural $n$. Using them pointwise does not
invoke an existing solver with a variable exponent.

Convert $\Phi$ to disjunctive normal form. In each conjunction give
every tree variable and every subexpression a code name, sharing all
uses of a variable. Keep all defining constraints positive, even for
a subexpression inside a disequality. Definitions are

$$
Z=[0],\quad Z=[1],\quad Z=\tau_{a(\mathbf z)}X,
                  \quad Z=J(X,Y).
\tag{NCE.12}
$$

For every $J$ occurrence choose either the collapse case
$X=[r+1],Y=[r],Z=[r+2]$, $r\in\mathbb N$, or the constructor case
$Z=F(X,Y)$ with normality required. There are finitely many choices
from the expression graph, regardless of parameter sizes. At a fixed
assignment every actual solution chooses one of these cases, and
normal solutions of any chosen case expand to its native definition.

Erase ranks, writing $c$ for a primitive shape and $f$ for the free
binary shape constructor. The positive shape equations are: primitive
names have shape $c$; shift and equality constraints identify shapes;
and a constructor definition gives $s_Z=f(s_X,s_Y)$. These equations
contain no parameters. Solve them by finite first-order unification
with the finite-tree occurs check. A failed branch has no finite
solution. For a successful branch take an idempotent most general
unifier, giving finite terms $S_Z$ over $c,f$ and remaining shape
variables $w_1,\ldots,w_s$. Every actual finite shape solution factors
through these terms. The occurs check is applied to free shapes only,
after native collapse splitting; for instance the native solution of
$\rho x=\langle x,\alpha\rangle$ at $x=\beta$ is not discarded.

Decorate every explicit $c$ occurrence of $S_Z$ with its own scalar
rank. Decorate each occurrence of $w_j$ with its own block name of
sort $j$. Different occurrences of the same shape variable are not
identified as values. Every use of one code name reuses its entire
decorated template. This preserves both source occurrence sharing
and any distinct subtrees that merely have the same shape.

Traverse each positive equation through its identical unified shapes.
Each aligned $c$ pair gives a scalar equation
$r_u-r_v=a(\mathbf z)$; each aligned $w_j$ pair gives a whole-block
equation $U_u=U_v+a(\mathbf z)$. A constant definition supplies an
equation to rank zero, and collapse supplies offsets $1$ and $2$.
For $Z=F(X,Y)$ compare $S_Z$ with $f(S_X,S_Y)$ at offset zero.
Thus the only remaining equations are scalar differences and
same-sort whole-block differences. A scalar cannot be compared with
a residual block: their unified shape positions would be $c$ and
$w_j$, contradicting identical terms. Nor can different residual
sorts be compared. Reassembly of these aligned constraints recovers
every positive code equation. This is NSF Lemma 3.2 with affine labels.

At every explicit $c/c$ cherry in every named template impose
$r_L-r_R\ne1$. For each negative comparison $X\ne Y$, if $S_X=S_Y$
syntactically, choose a mismatching aligned scalar or whole block.
This is a finite disjunction, since the template is finite. Distribute
these choices jointly for all negative comparisons. If $S_X,S_Y$
are syntactically different, reserve that negative comparison for
shape separation. These choices include all original negative atoms;
no class inequality or link is dropped. Choosing a mismatch of a
block with itself yields an impossible arithmetic branch, as required.

Use the nonleaf markers of [NSF, Lemma 4.1][NSF]. More explicitly,
let $L$ be the maximum of $1$ and the leaf counts of all $S_Z$,
counting each residual occurrence as one leaf, and choose
$M=\max(3,L+1,s+1)$. For each sort choose a different ground full
ordered shape $G_j$ with $M$ leaves. A root joining left and right
combs with $j$ and $M-j$ leaves gives at least $M-1$ choices.
There are no markers to choose when $s=0$.

These choices preserve every syntactic shape inequality in the finite
list. At a first disagreement, different variables get different
markers; a marker has $M$ leaves and cannot equal $c$; a ground
compound subterm has fewer than $M$ leaves; and a compound containing
a variable has more than $M$ leaves after substitution. A
constant/constructor disagreement stays a constructor disagreement.
This argument also covers subterms of listed terms, whose leaf counts
are no larger. Marker selection is independent of $\mathbf z$.

Replace each block name $U$ of sort $j$ by $G_j$ with one scalar
$b_U\in\mathbb N$ on every leaf. Translate its whole-block relations
to differences of those scalars, keeping their affine labels. Retain
every explicit rank constraint and explicit cherry inequality. The
result is a finite scalar system $A_b(\mathbf z,\mathbf r)$ of the
form (NCE.6), together with its fixed zero and nonnegativity. It has
no scalar/block comparisons and no hidden arithmetic constraints.

For soundness, every inserted marker is normal: a primitive cherry
inside it has equal ranks, never consecutive descending ranks. Its
root is nonleaf, so insertion creates no primitive cherry at a
template/marker boundary. All other primitive cherries are the
explicit ones whose inequalities were imposed. Every named code is
therefore normal. The aligned constraints reassemble all positive
definitions. A reserved shape inequality holds by marker separation;
every other negative comparison has its chosen mismatch. Formula
(NCE.11) then expands one consistent valuation of all names to a
native solution of the chosen original conjunction. In particular,
$Z=\tau_aX$ with natural ranks in $X$ forces every rank in $Z$ to be
at least $a$, exactly the supplied image condition. Negative labels
in a difference graph are integer differences, not native inverse
operations.

For completeness, fix an arbitrary guarded $\mathbf z$ and an
arbitrary finite native solution. Its evaluated normal codes select
the collapse branch and factor through the shape unifier. Read the
explicit scalar ranks; they satisfy every explicit cherry condition.
For each negative comparison with identical symbolic shapes, select
an actually differing aligned scalar or block. An actual residual
shape may be primitive or compound, but its leaf set is finite and
nonempty. Its block decorations solve the same-sort functional system
at this very $\mathbf z$. Lemma 3.3 replaces those functions by
constant ranks on the preselected $G_j$, simultaneously for all
sorts. The explicit scalar ranks can be left unchanged. No constraint
ties them to a residual block. Replacing a primitive residual by a
nonleaf may remove a boundary cherry but creates none. All selected
constraints survive, and syntactically different shapes become
separated. Hence $A_b(\mathbf z,\mathbf r)$ has a solution at the
unchanged parameter tuple.

Finally apply Lemma 3.2 to $A_b$, obtaining $Q_b$ and its finite rank
extractor. Boolean branching, collapse splitting, finite unification,
template expansion, negative splitting, marker selection and graph
traversal all terminate before parameter values are chosen. The two
preceding paragraphs prove both directions of (NCE.10), not merely
separate decisions after supplying the parameters. Every returned
rank is a finite natural, so expansion by $E$ terminates. $\square$

**Corollary 4.3 (the precise projection and its limits).** The theorem
constructs a quantifier-free affine formula for parameter support.
Splitting $a\ne b$ into $a\le b-1$ or $b\le a-1$ shows that this
support is a finite union of integer points in rational polyhedra,
also intersected with the supplied guard. Its nonemptiness is decidable,
and a semilinear representation is effectively obtainable.

Proof. Every output condition is explicitly affine. Distribute the
finite Boolean guard and the displayed disequality alternatives.
Presburger sentence decision and effective semilinear conversion are
the established results of Ginsburg--Spanier, Theorems 1.2--1.3 [GS].
They are applied only after the native variables have been removed
by Theorem 4.2. Arithmetic model extraction can, for example, follow
a positive decision by enumeration of natural tuples; termination
then follows from that decision's positive certificate of existence.
The negative decision never relies on such enumeration. $\square$

The quantifiers are
$\forall\mathbf z\,[\exists\mathbf x\ \Phi
\leftrightarrow\exists b,\mathbf r\ A_b]$ under the guard.
Neither the source nor the scalar ranks must remain the same as
$\mathbf z$ varies. Even at one $\mathbf z$, marker replacement can
change source shape and identity. The formula does not define all
normal codes in the ambient language excluded by [TPO][TPO], does
not give a source-preserving truncation, and does not represent all
solutions of arbitrary tree-quantifier alternations.

## 5. The complete signed chronological relation

**Theorem 5.1 (exact signed epoch support, existence and extraction).**
For every input of Definition 1.2 there is a terminating construction
of a finite affine formula $F_I(\mathbf n)$ with

$$
F_I(\mathbf n)\quad\Longleftrightarrow\quad\mathbf n\in E_I.
\tag{NCE.13}
$$

For valid input its form is

$$
F_I(\mathbf n)=\operatorname{Chron}(\mathbf n)
                   \land\bigvee_{b\in\mathcal A_I}Q_b(\mathbf n).
\tag{NCE.14}
$$

The construction decides $E_I=\varnothing$ with terminating YES and
NO outcomes, without an inhabitation premise. For every tuple accepted
by $F_I$, it constructs one finite $t$ realizing every complete row
and every signed link at those exact epochs. It also constructs a
feasible tuple and such a source whenever $E_I\ne\varnothing$.

Proof. Validate the finite input. On valid input apply Theorem 4.2 to
(NCE.4), with parameters $\mathbf n$, tree variables consisting of
the single $t$ and all the $x_{i,b}$, and guard
$\operatorname{Chron}(\mathbf n)$. All exponents are coordinates
$n_i\ge0$. Proposition 2.2 supplies both native correspondences.
The source witness is the expansion of that one named source template;
the hole values returned in the same valuation satisfy its row
equations. No source is chosen separately for an individual row or
link. Completeness in Theorem 4.2 keeps the original epoch tuple,
even when it replaces the original source.

Decide the Presburger sentence $\exists\mathbf n\ F_I(\mathbf n)$.
This terminates in the empty case as well as the nonempty case. On
a supplied accepted tuple, evaluate the finite branches, choose a
true one, compute its rank potentials and bases, and expand its
source. On global nonemptiness first extract an arithmetic epoch
tuple as in Corollary 4.3, then use the same construction. There is
no finite epoch cutoff and no unbounded negative search. $\square$

**Proposition 5.2 (edge cases and source-fiber distinction).** The
theorem retains the entire input domain, but its witness templates
are in general a strict subset of the source fiber.

Proof. An empty cut supplies a ground $W_i$; a root cut supplies one
class variable; a valid blocked row with no holes supplies a ground
context and an empty class tuple. Empty $\Lambda$ adds true. A
same-endpoint disequality becomes $x\ne x$ and rejects every branch;
an equality is harmless. Equal epochs are included by non-strict
chronology and are checked against the same iterate equations. A
later-born hole is constrained in $\rho^{n_i}t$ itself. None of the
construction stages assumes initial reachedness or a positive number
of class variables. All negative partitions and links are processed
in the same finite system.

For the distinction, one root-cut row at epoch zero with no links
admits every finite native tree. Any one finite list of fixed normal
shapes has a maximum number of normal leaves, while normal codes
with constant rank zero have arbitrarily many leaves and are all
normal. Thus those templates need not cover the entire source fiber.
Their sufficiency concerns existence at each epoch tuple, not a
bijection on original sources. Proposition 2.2 remains the exact
all-source presentation. NUE's row-only source-preserving result
retains its stronger fiber property in its own language. $\square$

**Corollary 5.3 (source-value uniqueness remains decidable).** Even
with signed unknown-epoch input, one can decide whether the original
tree value is identical in all realizing histories, after first
checking nonemptiness. If unique it is recoverable; otherwise two
different originals and their full realizing epoch tuples can be
returned.

Proof. Extract $(t_*,\mathbf n_*)$ from Theorem 5.1. Add the ground
native disequality $t\ne t_*$ to (NCE.4), and apply Theorem 4.2 with
the same chronology guard. A positive answer returns a different
original and its joint history. A negative answer proves that all
originals equal $t_*$. The added finite ground term belongs to
(NCE.9); no free unknown tree parameter or all-source template
parametrization is needed. This extends the row-only uniqueness
consumer [NUE, Theorem 4.1][NUE] through the new support theorem.
$\square$

## 6. Exactly which relative times the input determines

**Definition 6.1 (lag support and identifying components).** For
$a,b<m$ put

$$
D_{ab}(I)=\{n_b-n_a:\mathbf n\in E_I\}\subseteq\mathbb Z.
\tag{NCE.15}
$$

For $a\le b$ this lies in $\mathbb N$. On a nonempty $E_I$, say
$a\sim_I b$ when $D_{ab}(I)$ is a singleton, and denote its value
by $d_{ab}$. This is identification from the entire retained input,
including the exteriors, complete partitions and all signed links.

**Theorem 6.2 (effective full lag test).** The support $D_{ab}(I)$
has an effective Presburger description. Nonemptiness and uniqueness
of each lag are decidable. On consistent input, unique lags are
recoverable; for each nonunique lag two complete realizing histories
with different values can be returned. Inconsistent input is not
classified as unique by vacuity.

Proof. Use $\exists\mathbf n\,[F_I(\mathbf n)\land
d=n_b-n_a]$ as the description, with an integer $d$ or the two
nonnegative coordinates of an integer encoding when needed. First
decide $E_I\ne\varnothing$ and extract $\mathbf n_*$. Let
$d_*=n_{*,b}-n_{*,a}$. Decide

$$
\exists\mathbf n\quad F_I(\mathbf n)
                         \land n_b-n_a\ne d_*.
\tag{NCE.16}
$$

A negative answer gives the unique lag. A positive answer gives
another tuple, and Theorem 5.1 supplies a common finite source for
each of the two alternative histories. The sources may differ
between alternatives; each history separately has one source shared
by all its records. Two different lag values on the same input
exclude a deterministic exact lag decoder from those data alone.
$\square$

**Corollary 6.3 (relations among identifiable relations).** On
consistent input, $\sim_I$ is an effectively computable equivalence
relation, and its offsets satisfy

$$
d_{aa}=0,\qquad d_{ba}=-d_{ab},\qquad
d_{ac}=d_{ab}+d_{bc}\quad(a\sim_I b\sim_I c).
\tag{NCE.17}
$$

Its component containing record zero identifies exactly the individual
epochs fixed by the input. Adding signed links shrinks $E_I$ and
every lag support. The added memory newly identifies $n_b-n_a$
exactly when its refined support is nonempty and singleton while
the lag support after deleting those links has at least two values.

Proof. Every difference identity in (NCE.17) holds at each common
epoch tuple, and nonemptiness gives at least one such tuple. Constancy
therefore gives reflexivity, symmetry and transitivity with those
offsets. Since $n_0=0$, $d_{0b}=n_b$ precisely when that epoch is
constant. Link addition is conjunction on the same history set, so
gives the stated inclusions and the exact criterion for new recovery.
After one feasibility query and witness, at most $\binom m2$ queries
of (NCE.16) compute all components. Connectivity of the input link
graph is not this computed equivalence relation. $\square$

**Proposition 6.4 (local orbit offsets, including births).** Fix an
actual finite source $t$. For each address $p$ that occurs in the
history, let $b_p$ be its first reached epoch. Put
$v_p=(\rho^{b_p}t)|_p$ and use [ABC, Corollary 2.4][ABC] to write
$B(v_p)=\tau_{a_p}Z_p$ uniquely, where $a_p\in\mathbb N$ and the
minimum primitive rank of $Z_p$ is zero. For $n_i\ge b_p$ and
$n_j\ge b_q$,

$$
(\rho^{n_i}t)|_p=(\rho^{n_j}t)|_q
\quad\Longleftrightarrow\quad
Z_p=Z_q\ \land\
n_j-n_i=(a_p-b_p)-(a_q-b_q).
\tag{NCE.18}
$$

Under the same two guards, disequality is the complement of the
right side. In particular a reached same-address comparison gives
equality exactly at zero lag.

Proof. Once reached, a subtree is transported by each subsequent
iterate, as in [NSF, Lemma 9.2][NSF] and
[NativeDepthPatterns][DEPTH], `original_present_transport`, applied
with the capture tree as its starting source; see [its Scribe][DEPTH-S].
Its code is consequently $\tau_{a_p+n_i-b_p}Z_p$.
Uniqueness of minimum-rank normalization gives (NCE.18). Each
address eventually occurs by the same supplier's saturation result,
so the first reached epoch exists. Transport starts there and never
asserts a subtree before its birth. For $p=q$ the two intrinsic
offsets coincide, leaving lag zero. $\square$

The $Z_p,a_p,b_p$ in (NCE.18) are consequences of one actual source.
They are not independent advice variables that may be assigned per
edge. Their compatibility, finite occurrence structure and all
negative constraints are carried jointly by (NCE.4). A necessary
clock equation alone does not replace Theorem 5.1.

## 7. Complete native comparison histories

**Application 7.1 (a root-certificate row family).** Let
$p=e_1\cdots e_h\ne\varepsilon$, put
$w(p)=\#_L(p)+2\#_R(p)$, and let $\bar L=R,\bar R=L$.
Define the full path frontier

$$
P(p)=\{p\}\cup\{e_1\cdots e_{j-1}\bar e_j:1\le j\le h\}.
\tag{NCE.19}
$$

Its exterior is the full path context, all of whose leaves are holes.
Give it the complete partition $q\sim q'$ exactly when $w(q)=w(q')$;
call this row $R(p)$. Consider three records: root-cut singleton rows
at epochs $0,a$, and $(P(p),R(p))$ at epoch $b\ge a$. Retain the
link equating the root hole at epoch $a$ to the hole $p$ at epoch $b$.
Then the exact epoch support is

$$
\{(0,a,a+w(p)):a\in\mathbb N\}.
\tag{NCE.20}
$$

At such a tuple the entire original-source fiber is
$\{T_s:s+a\ge\eta(p)\}$, where $\eta(p)=1$ if the last letter
is $L$, and $\eta(p)=0$ if it is $R$.

Derivation from the supplier. [ARH, Theorem 4.2][ARH] already
classifies the guarded root-to-descendant record at any supplied
$a,b$: it forces $b=a+w(p)$ and exactly those atomic originals.
This application adds no new root-certificate rigidity theorem.
It remains to check the proposed complete last row, rather than
only the linked endpoint. On $t=T_s$ the last tree is
$T_{s+a+w(p)}$. The guard for $p$ is precisely
$s+a\ge\eta(p)$ by [ARH, (4.3)][ARH]. Every sibling of its path
is also reached. At each frontier hole $q$ its whole value is
$T_{s+a+w(p)-w(q)}$. Atomic index injectivity makes the full
partition exactly the one specified above. All proper prefixes in
the path context are branches, so its entire exterior is correct.
This proves both inclusions of the asserted history and source
fibers. The single source $\beta=T_1$ witnesses every tuple in
(NCE.20). With the link deleted, the same three rows admit every
$0\le a\le b$: choose $t=T_s$ with $s+b$ large enough to reach
the whole frontier and use the same weight calculation.

Thus a literal addressed relation can recover an arbitrarily late
exact relative lag without fixing the source or the earlier epoch.
Every positive integer lag occurs by taking $p=L^h$. The address
and full partition are part of the input, not a free numerical offset.
For $p=LL$, for example, the frontier is $\{R,LR,LL\}$ and its
partition equates $R$ with $LL$, while $LR$ is distinct. Ignoring
this repeated class would change the example's record.

**Application 7.2 (calibrated and uncalibrated cross-cone memory).**
Use an initial empty-cut row fixing
$t_d=\langle T_d,\alpha\rangle$, where $d\ge1$. At later
epochs $a\le b$ use the two-hole cut $\{L,R\}$ with two distinct
classes. The link earlier $L$ equals later $R$ gives exactly
$b-a=d$; replacing its sign by disequality gives exactly $b-a\ne d$.
Both statements allow arbitrarily late $a$.

The calculation is
$\rho^a t_d=\langle T_{d+a},T_a\rangle$ and
$T_{d+a}=T_b\leftrightarrow b-a=d$. The case $d=1$, including
its failure under every shared finite cap, is already
[NUE, Proposition 6.3][NUE]; it is a supplier, not the new support
argument of this volume.

If instead the initial row is also the two-hole distinct-class row,
the same equality at the later captures gives exactly
$\{(0,a,b):0\le a<b\}$. Ties would contradict the within-row
disequality. Conversely each positive $d=b-a$ has the common source
$t_d$, whose three complete rows and link have the prescribed form.
Thus an equality bit without the calibration does not determine a
positive numerical offset. Application 7.1 identifies its offset
through the root/descendant relation and literal path, a different
constraint from this uncalibrated cross-cone comparison.

**Application 7.3 (born endpoints and invalid old endpoints).** Let
the epoch-zero cut be $\{LL\}$ with exterior $\alpha$ and no
holes. It fixes $t=\alpha$ while retaining its blocker. Let the
later row have cut $\{L,R\}$ and two distinct classes. With no
links its support is exactly $\{(0,n):n\ge2\}$: $T_0,T_1$ are
leaves, and $T_n=\langle T_{n-1},T_{n-2}\rangle$ for $n\ge2$.
Both later holes are born positions. A proposed link using the old
endpoint $(0,LL)$ is rejected for either sign, despite valid later
endpoints. The absent old endpoint is not a hidden variable.

**Proposition 7.4 (joint negative memory can obstruct every source).**
Take three root-cut rows and the links $H_0=H_1$, $H_1=H_2$,
$H_0\ne H_2$. Every proper subset of these three links has a
chronological finite common-source realization, but the whole input
has none.

Proof. The whole conjunction violates equality transitivity. For
the three two-link subsets use respectively epoch tuples $(0,0,0)$,
$(0,0,1)$ and $(0,1,1)$ on source $\alpha$, assigning the tuple
with a tie to the equality edge that remains. More explicitly,
the two positive links use $(0,0,0)$; the first positive and the
negative use $(0,0,1)$; the second positive and the negative use
$(0,1,1)$. Their positive and negative root comparisons are correct
because $T_0\ne T_1$. Smaller subsets follow. These are separate
witnesses for separate subproblems; they cannot be glued into a
witness of all three. The stronger row-only finite-occurrence
obstructions of [NUE, Propositions 5.1--5.2][NUE] are also retained.
$\square$

**Application 7.5 (time uniqueness without source identity).** Two
root-cut rows linked by equality have exact support $\{(0,0)\}$
and admit every $t\in\mathcal T$. Indeed a positive iterate raises
the minimum primitive rank of $B(t)$, so cannot equal $t$.
Changing the sign gives exactly the positive lags. A cyclic leafless
infinite tree would invalidate this reasoning and admit positive
equalities, which is why the finite-tree occurs check and the
nonempty leaf sets in the proof cannot be omitted.

## 8. Representation, expansion and physical acquisition

**Definition 8.1 (separate resource quantities).** Let the input size
count all literal exterior nodes, all delivered address symbols,
partition data, link endpoints and signs, and binary integer
coefficients. For one constructed branch let $C$ count smart-pair
sites, $L$ bound the fully expanded shape-template leaf counts,
$s$ count residual sorts, and $D$ count its scalar disequalities.
These are finite syntax quantities, distinct from the sizes of
unknown sources and the numerical values of epochs.

**Proposition 8.2 (finite construction and output bounds).** There
are at most $2^C$ collapse choices per propositional branch. If
$d$ code disequalities have identical templates, there are at most
$\max(1,L)^d$ choices of mismatch locations. With
$M=\max(3,L+1,s+1)$, every resulting named witness template has at
most $ML$ primitive leaves. For a fixed accepted parameter tuple,
the scalar extractor uses at most $D+1$ trials per free equality
component and returns ranks at most $2K+D$, with $K$ as in Lemma 3.2.

If the source code has primitive ranks $r_1,\ldots,r_\ell$, its
expanded native tree has exactly

$$
2\sum_{j=1}^{\ell}F_{r_j+1}-1
\tag{NCE.21}
$$

nodes, where $F_0=0,F_1=F_2=1$.

Proof. Each pairing has two cases and each identical-template
negative comparison has at most $L$ primitive or residual positions.
Replacing each residual leaf by an $M$-leaf marker gives the stated
template bound. Lemma 3.2 gives the rank trials and bound. The atomic
recurrence gives $F_{r+1}$ leaves in $T_r$; expansion at the code
leaves adds these leaf counts. A nonempty full binary tree has twice
its leaf count minus one nodes. $\square$

Explicit unifier expansion and branching may enlarge the representation;
these bounds do not assert a polynomial construction in the original
input size. Membership in the constructed support is finite affine
evaluation. Global existence is a finite integer-arithmetic decision,
not a measured solver runtime or a claimed tight complexity class.
Semilinear conversion is optional and can enlarge the description.
Rank bit lengths do not pay the expansion cost (NCE.21), and a
bounded normal shape is not a bound on the native sizes of all sources.

**Assumption 8.3 (conditions for operational use).** An operational
consumer must be supplied a producer bridge establishing that its
rows and links were acquired on one continuing native register under
the stated concurrency contract. Source evidence consists of actual
replies to $\mathsf{Read}(p)$ at fully materialized literal addresses,
with replies in $\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$,
and lawful forward updates.
Exact comparisons must use acquired operand descriptions or another
proved paid comparison procedure. An old row that erased its hidden
values does not itself supply their descriptions for a later comparison.

Charge every actual read, the sum and maximum of literal address
lengths, address generation and delivery, full descriptions, local
comparison work, workspace, storage between captures, retained rows
and signs, actual updates, validation failures, cleanup and handoff.
Indices and lengths must be represented at their actual bit costs.
The final accessible state must not retain unlisted source information
in caches, control, timing or archives. These requirements are
premises for a physical interpretation, not extra operations provided
by the offline support algorithm.

**Proposition 8.4 (semantic reconstruction is not provenance).**
Theorems 5.1, 5.3 and 6.2 do not authenticate an actual past history,
identify a physical register, or supply a native producer at their
arithmetic decision cost. A unique relative update count does not
determine a physical elapsed duration.

Proof. Their mathematical inputs are unchanged if a finite record
tuple is copied or proposed without any acquisition. The output is
therefore unchanged, whereas the claimed acquisition or register
identity can differ. Those are not predicates of the semantic
input. Durations between updates are likewise absent from (NCE.1)--(NCE.2).
Once Assumption 8.3 is supplied, the actual history belongs to
$\mathscr H_I$ and a constant target on that fiber is recoverable;
membership cannot establish the assumption itself. $\square$

**Definition 8.5 (operational supplier limits and remaining problem).**
[NativeActiveParityExecution][ACTIVE],
`native_active_parity_execution`, uses a supplied full source skeleton,
independent leaf labels, a bound $t\le2K$, and the condition that
the number of leaves is even or $t=0$; [its Scribe][ACTIVE-S] states
the corresponding active parity execution. These are not hypotheses
of the present arbitrary unknown-epoch input.
[NativeClassRootSimulation][ROOT], `truthful_joint_root_simulation`,
fixes a stationary one-step image/origin setting, a supplied finite
supplement map on complete valuations, and finite dialogues assumed
correct on those origins; [its Scribe][ROOT-S] preserves that scope.
Neither result supplies a general concurrent producer of the present
multiple-capture signed input merely because it uses native reads.

The exact mathematical support, negative decision and finite witness
construction have the proofs above. A complete paid producer for
arbitrary retained cross-epoch links under an independently advancing
writer, optimal acquisition/workspace/retention tradeoffs, unrestricted
variable-address or all-depth recovery, and source-preserving finite
parametrizations of all signed fibers are separate unresolved tasks.
The broader recursive mutual recovery of space, time, boundary and
memory is not completed by this finite existential result. No physical
spacetime unity or worldwide originality claim follows.

## 9. Source correspondence and literature boundaries

**References 9.1 (repository mathematical correspondence).** The
native identification in the cited Lean sources is
$\alpha=\mathtt{FreeMagma.of\ true}$,
$\beta=\mathtt{FreeMagma.of\ false}$, pairing
$=\mathtt{FreeMagma.mul}$ and
$\rho=\mathtt{GenealogicalFiberTransport.substitution}$.
The normal-code and fixed-power existential suppliers are the ordinary
theorems of ABC and NSF; they are not attributed to a newly compiled
Lean solver. The following declarations delimit additional reuse.

| Source and corresponding Scribe | Supplied statement and boundary |
| --- | --- |
| [NativeCutFibers][CUT], [Scribe][CUT-S] | `rowFiberEquiv` identifies legal entire class valuations with the complete actual row fiber. NUE applies it to finitely validated proposed rows. |
| [ActualCutPartitionDecoder][ROW], [Scribe][ROW-S] | `canonicalRow_record_iff` equates canonical-row equality with addressed exterior and full partition equality; it does not eliminate epoch variables. |
| [NativeHistoryCells][CELL], [Scribe][CELL-S] | `cell_feasibility_exact`, using private `syntax_iff_ground`, tests fixed literal-history cells and every old-class inequality. Its depth guard and fixed histories are not a parametric morphism-power interface. |
| [NativePredecessorRowRecovery][BACK], [Scribe][BACK-S] | Private `delta_sigma` proves opaque parsing after one substitution; the public recovery theorem retains actual old occurrences, including born/old distinctions. It is one-step recovery, not unknown-epoch support. |
| [IntrinsicSubstitutionCoordinates][INTR], [Scribe][INTR-S] | `intrinsic_coordinates` gives the maximum legal predecessor depth and unique primitive endpoint on every finite tree. It supplies faithful source coordinates, not independently assignable clocks for unrelated endpoints. |

The substantive additional content is Theorem 4.2's uniform extension,
the exact signed consumer in Theorem 5.1, and the uniqueness and lag
consumers. The complete-row compilation, fixed-shift normal machinery,
root-certificate classification, and cap obstruction retain their
existing suppliers. Reading a declaration and its Scribe is not a
new kernel verification of its application.

**References 9.2 (primary literature and admissible transfer).** The
following primary statements delimit the arithmetic and alternative
routes. Each is `literature-attested` in the indicated scope; the
native bridge is the argument of Sections 2--5.

| Primary source | Exact use or missing correspondence |
| --- | --- |
| Ginsburg and Spanier, *Semigroups, Presburger Formulas, and Languages*, Pacific Journal of Mathematics 16(2), 285--296, Theorems 1.2--1.3, [publisher text][GS] | Decidability of natural-number Presburger sentences and effective conversion between Presburger and semilinear descriptions. These supply arithmetic decision and conversion after (NCE.10), not elimination of native trees. |
| Marshall, Meadows and Narendran, *On Unification Modulo One-Sided Distributivity: Algorithms, Variants and Asymmetry*, arXiv:1503.06687v2, Sections 4--5, Theorems 4.4 and 5.8, [primary text][MMN] | The typed single-homomorphism theory and its subterm-collapse-free cycle arguments have their stated laws. Native $\rho\beta=\langle\beta,\alpha\rangle$ supplies additional interpreted behavior. No raw native occurs-check rule is imported; only ordinary free-shape unification is used after collapse splitting. |
| Cerna, *Schematic Unification*, arXiv:2306.09152v7, Definitions 2--6 and Section 6, [primary text][CERNA] | Indexed-variable substitution schemas ask whether all iterated schematic instances are unifiable; the sound terminating algorithm has completeness under infinity-stability. That quantifier order and premise do not supply existential joint finite native epochs and one ground original. |
| Kuncak and Rinard, *On the Theory of Structural Subtyping*, arXiv:cs/0408015v1, Sections 6.1--6.4, Theorem 90 and Corollary 91, [primary text][KR] | Term-power quantifier elimination and decision concern the exact Figure 9 language with Figures 10--11 semantics. No unproved native-normal-domain predicate or outer scalar/selected-leaf operation is added. Formula-dependent existential markers avoid, rather than solve, the interpretation obstruction in TPO. |
| Barguñó, Creus, Godoy, Jacquemard and Vacher, *Decidable Classes of Tree Automata Mixing Local and Global Constraints Modulo Flat Theories*, arXiv:1302.6960v2, Section 2.4 and Theorem 5.22, [primary text][BCGJV] | Flat equations have equal side heights at most one and the same variable support; the stated automaton emptiness theorem uses its own computable run-height bound. Neither interpreted native substitution nor existential iteration parameters have been encoded into that grammar here. It is not a black-box native support solver. |
| Atserias and Kolaitis, *Consistency, Acyclicity, and Positive Semirings*, arXiv:2009.09488v1, Theorems 3--4, [primary text][AK] | Local-to-global consistency for positive-semiring relations is characterized by acyclicity of the attribute hypergraph. Separate nonempty native pair witnesses are not its marginal-consistency premises. A binary source tree or a connected comparison graph does not establish the required schema condition. |

This is a limited comparison with homomorphism unification, symbolic
iteration, term powers and local/global tree constraints, not an
exhaustive absence or novelty claim. No inaccessible or unread paper
is a premise. The construction's exact source and quantifier
correspondence is proved in this volume; generic decidability results
are not invoked with enlarged languages.

[NUE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_UNKNOWN_EPOCH_GLUING.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[NIS]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_SATURATION.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[CUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[CUT-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.scribe.cs
[ROW]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[ROW-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.scribe.cs
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[DEPTH-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.scribe.cs
[CELL]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[CELL-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.scribe.cs
[BACK]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.lean
[BACK-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.scribe.cs
[INTR]: ../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean
[INTR-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.scribe.cs
[ACTIVE]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.lean
[ACTIVE-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.scribe.cs
[ROOT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.lean
[ROOT-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.scribe.cs
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[MMN]: https://arxiv.org/html/1503.06687v2
[CERNA]: https://arxiv.org/html/2306.09152v7
[KR]: https://arxiv.org/pdf/cs/0408015v1
[BCGJV]: https://arxiv.org/pdf/1302.6960v2
[AK]: https://arxiv.org/html/2009.09488v1

## 追加锚（本行以下为增补区）

## 10. Regular memberships at shared affine native epochs

**Definition 10.1 (finite native membership language).** Retain exactly
$\mathcal T,\rho$ and literal equality from Definition 1.1. Let
$\mathbf z\in\mathbb N^k$ be a finite tuple. Expressions have grammar
(NCE.9); a supplied Presburger condition $G(\mathbf z)$ requires every
specified integer-affine exponent to be nonnegative. Let $\Phi$ be any
finite Boolean combination of

$$
A=B,\qquad A\in L_i,
\tag{NCE.22}
$$

where each $L_i$ is supplied by a finite tree automaton over the fixed
ranked signature $\alpha:0,\beta:0,\langle\ ,\ \rangle:2$. Membership
is tested on the expanded native value of $A$. Automata are fixed input
descriptions, independent of the values of $\mathbf z$. All tree variables
are jointly existential finite native trees. Every occurrence of a name
uses the same whole value, including occurrences beneath different powers.

There are no free unknown tree parameters, rational or infinite trees,
variable addresses, arbitrary homomorphisms, products of epoch parameters,
tree-quantifier alternations or numerical leaf-count operator. A supplied
finite ground tree is its literal constructor expression. Negated
membership and whole-tree disequality are included by Boolean negation.
The guard may contain scalar quantifiers; these are ordinary Presburger
quantifiers and do not quantify native trees.

**Theorem 10.2 (exact Presburger support with joint witnesses).** There is
an effective construction of a Presburger formula $F_{G,\Phi}(\mathbf z)$
such that, for every identical tuple $\mathbf z$,

$$
F_{G,\Phi}(\mathbf z)
\quad\Longleftrightarrow\quad
G(\mathbf z)\land
\exists\mathbf x\in\mathcal T^r\ \Phi(\mathbf z,\mathbf x).
\tag{NCE.23}
$$

At any accepted tuple the construction gives one simultaneous finite
native assignment satisfying every atom and every repeated occurrence.
It decides global nonemptiness and, in the nonempty case, gives a tuple
and such an assignment. No epoch, tree-size or residual-depth bound is
an input premise. The proof is given in Sections 11–12.

The output may require congruences. It does not claim the stronger
quantifier-free affine-polyhedral format of Theorem 4.2, nor a
parameter-independent finite list of witness shapes. Theorem 4.2 remains
the equation-only supplier. [SFP, Theorem 4.1][NCE-SFP] already preserves
every source and every leaf rank using supplied arbitrary residual shapes;
(NCE.23) instead decides existential support and may replace a realizing
source even at one fixed tuple.

## 11. The common-shape rank automaton

**Lemma 11.1 (primitive-state arithmetic).** Complete and determinize the
supplied automata and take their finite product. Write its state set as
$Q$, leaf states as $q_\alpha,q_\beta$, and pair transition as
$\delta:Q^2\to Q$. If $q_r$ is its state on $T_r=\rho^r\alpha$, then

$$
q_0=q_\alpha,\qquad q_1=q_\beta,\qquad
q_{r+2}=\delta(q_{r+1},q_r).
\tag{NCE.24}
$$

For each $s\in Q$, the predicate $q_r=s$ on $r\in\mathbb N$ is effectively
Presburger.

Proof. This is the primitive-state orbit of [NRF, Definition 4.1][NCE-NRF].
The pair $(q_r,q_{r+1})$ follows a deterministic map on the finite set
$Q^2$. Find its finite preperiod and positive period by the first repeated
pair. Each state preimage is then a finite set together with finitely many
arithmetic progressions. Their equalities, lower bounds and congruences
are Presburger formulas. The recurrence evaluates the actual $T_r$,
not a free unary-constructor encoding of its index. $\square$

**Definition 11.2 (one residual sort).** A shape is a finite full ordered
$c/f$ tree. Fix a finite nonempty set $V$ of block names sharing one
unknown shape $K$. A block $U_v$ assigns a natural rank to every leaf
of $K$. Supply finitely many pointwise equations and whole-block negatives

$$
U_u=U_v+a(\mathbf z),\qquad
U_u\ne U_v+b(\mathbf z),
\tag{NCE.25}
$$

with specified integer-affine $a,b$. An equation holds at every leaf;
a negative means that at least one leaf has the indicated rank mismatch.
Integer offsets are differences, not backward native operations.
Let $D$ index the negatives, retaining repeated demands. Also prescribe
one root state $s_v\in Q$ for the native expansion of every block.
Every block must be a normal code: at every sibling-leaf pair its left
rank minus its right rank is different from $1$.

For a state vector $\sigma\in Q^V$ and a mask $M\subseteq D$, let
$P_{\sigma,M}(\mathbf r,\mathbf z)$ assert that $\mathbf r\in\mathbb N^V$
satisfies all pointwise equations of (NCE.25), that $q_{r_v}=\sigma_v$
for every $v$, and that each negative $d=(u,v,b)$ has exactly the truth
specified by its bit:

$$
d\in M\quad\Longleftrightarrow\quad r_u-r_v\ne b(\mathbf z).
\tag{NCE.26}
$$

This is a Presburger formula by Lemma 11.1. A mask records an actual
mismatch, not distinct automaton states or universal pointwise inequality.

**Lemma 11.3 (guarded automaton for all simultaneous block values).**
There is a finite bottom-up automaton on $c/f$ shapes with finitely many
Presburger transition guards in $\mathbf z$ whose accepted nonleaf shapes
are exactly those supporting the blocks of Definition 11.2 with their
prescribed root states. Both directions use one rank field per block,
shared at every use of that block.

Proof. States consist of a leaf/nonleaf flag, a vector in $Q^V$, and a
subset of $D$. The $c$ transition to $(\mathsf{leaf},\sigma,M)$ has guard

$$
\exists\mathbf r\ P_{\sigma,M}(\mathbf r,\mathbf z).
\tag{NCE.27}
$$

At an $f$ node combine state vectors coordinatewise by $\delta$, take
the union of the two masks, and mark the result nonleaf. If at least
one child is nonleaf, this transition has guard true. If both are
leaves with annotations $(\sigma,M),(\sigma',M')$, its guard is

$$
\exists\mathbf r,\mathbf r'\quad
P_{\sigma,M}(\mathbf r,\mathbf z)\land
P_{\sigma',M'}(\mathbf r',\mathbf z)\land
\bigwedge_{v\in V}(r_v-r'_v\ne1).
\tag{NCE.28}
$$

Accept precisely nonleaf roots with vector $(s_v)_{v\in V}$ and mask
$D$. All of these states, transitions and formulas are constructed
before assigning the numerical parameters.

Given actual blocks, label each shape leaf by its simultaneous rank
tuple, native-state vector and exact mismatch mask. Bottom-up native
evaluation supplies the internal state vectors. Mask union records
precisely the negatives witnessed somewhere below. Normality supplies
(NCE.28). This is an accepting run.

Conversely fix an accepting run at one $\mathbf z$. For each primitive
cherry choose the two simultaneous rank tuples witnessing its particular
(NCE.28). For each leaf not in such a cherry choose a tuple witnessing
its (NCE.27). These choices are compatible: a leaf belongs to at most
one primitive cherry. Choosing a cherry witness can change the witness
for its child transition, but preserves that child's entire state vector
and mask. There is no other constraint between different shape positions:
all equations are pointwise, negatives require only the accumulated mask,
and normality compares ranks only at primitive cherries. Thus the chosen
ranks define every $U_v$ on the same $K$. All its pointwise equations hold;
every bit in $D$ has a genuine mismatch witness; and every block is normal.
Induction up the run gives its prescribed native root state. This proves
exactness without replacing ranks by constants or equating values that
merely share a finite state. $\square$

The joint guard (NCE.28) is essential. Testing two leaf transitions for
separate existence would not establish that their witnesses can also
satisfy every block's sibling normality. Requiring all mismatches at one
leaf would instead lose valuations whose negatives are witnessed at
different leaves. Mask union preserves those valuations.

## 12. Elimination of the shared native variables

**Construction 12.1 (finite structural cases).** Use ABC Theorems 2.2–2.3
and the flattening of Theorem 4.2, keeping its native normal coordinates
$[r],F$, smart pairing $J$, and translation $\tau_a$. These identities
hold at every natural $a$, so their use at $a(\mathbf z)$ preserves
that identical tuple. Convert the Boolean formula into a finite disjunction
of conjunctions. Negated regular membership uses the complement of a
completed deterministic automaton. Keep a shared code name for each tree
variable and each subexpression, with positive definitions even below
negative atoms. Split each $J$ into its actual collapse and ordinary
normal-$F$ cases, as in (NCE.11)–(NCE.12).

There is one additional structural split for each code disequality
$X\ne Y$: either their actual erased shapes differ, retaining that
$c/f$ term disequality, or their shapes agree, adding that equation to
the positive shape system. Solve all positive free-shape equations
jointly by an idempotent finite-tree unifier. An occurs-check failure
has no finite shape solution. This check is on $c/f$ only, after native
collapse splitting. It does not discard the native solution $x=\beta$
of $\rho x=\langle x,\alpha\rangle$.

The successful unifier supplies finite shape terms $S_Z$ in residual
variables $w_j$. Split every residual variable into the cases $w_j=c$
and $w_j$ nonleaf. Substitute $c$ in the first case before decorating
any template. The remaining residual variables have nonleaf roots;
their ground shapes need not be distinct. Retain all selected shape
inequalities after these substitutions, including any now impossible
ones. A later shape decision rejects an identical pair so obtained.

Decorate every explicit $c$ occurrence in each named template with a
scalar rank, and every residual occurrence with its own block name of
that residual sort. Every use of one code name reuses its decorated
template. Different block occurrences sharing a shape are not identified
as values. Traverse the positive definitions, shifts and comparisons
through their identical unified templates. They give scalar affine
rank equations or pointwise affine block equations within one residual
sort. There is no scalar/block alignment: a residual position in one
side is the same residual position on the other. Ordinary pairing aligns
the two children separately. Collapse gives primitive offsets $1,2$;
constants give scalar ranks $0,1$.

For every disequality assigned equal shapes, traverse the equal templates
and choose an aligned scalar or whole block at which the values differ.
This is a finite disjunction, distributed jointly across all negatives.
Retain each selected scalar mismatch or whole-block mismatch with its
actual affine offset. Any actual unequal codes on one shape select such
a position. Reassembly makes a selected mismatch sufficient. Disequalities
assigned unequal shapes retain the selected ground-shape inequality
instead. No syntactic shape disagreement is presumed to survive an
arbitrary residual substitution.

Require normality at each explicit $c/c$ cherry of every named template.
The nonleaf split ensures that there is no untested primitive cherry
across a template/residual insertion. Internal residual cherries will be
checked by Lemma 11.3. Thus these are all the normality requirements,
including those exposed when a residual was specialized to $c$.

**Construction 12.2 (membership reduction and the finite shape problem).**
Guess the product-automaton state of each explicit primitive occurrence
and of each residual block. The primitive guesses have the Presburger
conditions $q_r=s$ from Lemma 11.1. Evaluate each finite template bottom-up
with these guessed states and $\delta$, and require the accepting or
rejecting component specified by every membership atom. Normal expansion
uses actual native pairing at every $F$, so this evaluation tests exactly
the expanded native memberships. State equality does not replace any
positive or negative native comparison.

For each remaining residual sort apply Lemma 11.3 to all its block names,
pointwise equations and selected whole-block mismatches simultaneously.
This gives its regular shape domain by a finite transition table with
Presburger guards. Partition the parameter space by the complete truth
vector of all these finitely many guards. Each region $\Theta(\mathbf z)$
is Presburger. On that region every residual automaton is an ordinary
fixed finite $c/f$ tree automaton. The remaining shape question is exactly

$$
\exists K_1,\ldots,K_s\quad
\bigwedge_j K_j\in\mathcal L_j\ \land\
\bigwedge_\ell S_\ell(\mathbf K)\ne T_\ell(\mathbf K),
\tag{NCE.29}
$$

where the $\mathcal L_j$ are those fixed regular languages and all terms
use only $c:0,f:2$. Repeated occurrences of $K_j$ remain one variable.
Empty residual lists and ground shape inequalities are included.

For completeness of this final decision step, regular languages over
$c/f$ satisfy the admissibility hypotheses of Comon–Delor, Lemma 1,
Theorem 4 and Corollary 2 [NCE-CD]. Boolean combinations of these languages
are effective regular languages. The preimage of a regular state language
under $f$ is a finite union of products of child-state languages, obtained
from its finite transition table; the $c$ case is a finite leaf test.
Product determinization gives the same decomposition for Boolean sorts.
Emptiness and finiteness are decidable: trim the finite automaton to
productive states usable at an accepting root; an arbitrarily repeatable
state along a productive path gives unbounded height, while no such cycle
bounds accepting height. In the finite case enumerate all accepted trees
through that bound. These are precisely effective constructor
preimages and finite-sort operations required by admissibility.
Consequently the cited theorem decides (NCE.29), including all its shared
constructor-term disequalities. It sees no native $\rho$, integer rank,
free-power symbol or non-flat rewriting law. A product of automata, with
separate membership symbols for its accepting sets, supplies a single
finite regular-membership structure if required by the paper's notation.

**Proof of Theorem 10.2.** There are finitely many Boolean, collapse,
shape-equality, leaf/nonleaf, mismatch and state choices. Fix one such
choice and one guard region. The answer to (NCE.29) is a constant Boolean,
independent of the numerical tuple. If false discard this choice. If true,
conjoin its region with $G$ and all explicit scalar-rank equations,
mismatches, nonnegativity and primitive-state conditions. Existentially
project the finitely many scalar ranks. Taking the finite disjunction
constructs a Presburger $F_{G,\Phi}$.

For soundness at an accepted $\mathbf z$, extract scalar ranks, a solution
to (NCE.29), and accepting runs of the fixed shape automata. Lemma 11.3
chooses simultaneous local ranks at that same $\mathbf z$. Each named
normal code is then assembled once and reused at all of its occurrences.
Every positive aligned equation, collapse definition and ordinary-pair
definition reassembles. A negative either has different actual shapes or
its chosen genuine scalar/block mismatch. All primitive cherries are
normal, and bottom-up evaluation gives every demanded native membership.
Expanding by ABC's $E$ therefore supplies one joint original assignment.

For completeness, start with any original native assignment at a guarded
$\mathbf z$. Its normal codes select their actual collapse cases and
actual shape comparisons. Their shape solution factors through the
unifier; each residual selects its actual leaf/nonleaf case. Decorated
codes retain their actual scalar ranks and block fields. For each
same-shape negative choose an actual differing template position. Their
native states give the state guesses; their residual fields give accepting
runs by Lemma 11.3. Thus their shapes solve (NCE.29) on the selected guard
region, and their scalar ranks satisfy the remaining arithmetic at the
unchanged $\mathbf z$. This proves both directions of (NCE.23).

All constructions terminate. Arithmetic witness extraction can follow a
positive Presburger decision by finite-tuple enumeration. After a positive
shape decision one may enumerate finite shape tuples and their finite runs
until a solution to (NCE.29) is found; the decision proves this search will
terminate. At each local rank choice Presburger witness extraction likewise
terminates. Negative decisions use the terminating arithmetic and shape
deciders, not failed unbounded witness searches. Every expansion is finite.
Finally deciding $\exists\mathbf z\ F_{G,\Phi}$ gives global nonemptiness
and a parameter witness when nonempty. $\square$

**Remark 12.3 (why the new membership step is necessary).** The constant
rank-field replacement of Lemma 3.3 is an equation-only supplier, not a
membership-preserving operation. The singleton regular language
$\{\langle\alpha,\beta\rangle\}$ requires the normal code
$F([0],[1])$. A constant field on that residual shape cannot represent
this member. Lemma 11.3 keeps the two ranks jointly, and in general keeps
all finite native states and separately located mismatch witnesses.
Conversely $x=y\land x\ne y$, and
$x,y\in\{\alpha\}\land x\ne y$, still have no joint solution.
No independent witness per record or equality-by-state shortcut is used.

## 13. Fixed-capacity source realization and an original Rho label

**Convention 13.1 (actual apparatus and fixed numeral).** Use exactly
[ABT, Definition 18.1 and Convention 18.2][NCE-ABT]: the one GENERAL/ARC
installation $G_{\mathrm{gc}}$, its preparation occurrence $\xi$, actual
source16 and growing $\phi_K$, first Ready $P$ with source $\beta$ and
$H_0=h=K=1$, parked original client, occupied verifier and INITIAL consumer.
A completed call below is an actual outer01 call with canonical frame,
ReadState, generation, source/maintenance work, response, counters, rows,
actual delivery/check/ACK, source-token return, InnerReturn, CaptureCAP
and genuine Ready. Each next call begins after that return. The finite
supply and local-termination hypotheses are GENERAL Assumption 1.2's.
No outer00, history1 flight, reset, clone or new installation is used.

Fix a supplied numeral $h\ge1$. Let $\mathsf{HasBeta}$ be the language
of trees containing a beta leaf, and put
$L_h=\{u\in\mathcal T:\lambda(u)\le h\}$. Both are regular.
For $\mathsf{HasBeta}$ use an occurrence bit, with pair transition OR.
For $L_h$ use states $1,\ldots,h,\mathsf{overflow}$, leaf state $1$,
and truncated addition at a pair, accepting the numeral states. This
is an automaton for each supplied $h$, not one automaton with an unknown
numerical cutoff.

**Theorem 13.2 (exact attained chronological source-value projection).**
The logical source-value image of completed canonical source-only extensions
from this same $P$, allowing the installed Reserve/Raise maintenance, is
exactly $\mathsf{HasBeta}$. At final guard/reserve $h=K$ its image is
exactly $\mathsf{HasBeta}\cap L_h$.

More precisely, for every $t\in\mathsf{HasBeta}$ and every tuple
$0=n_0\le\cdots\le n_{m-1}$ with
$\rho^{n_{m-1}}t\in L_h$, there is a finite actual extension which first
constructs $t$ with accepted-Rho epoch zero and guard/reserve $h$, then
performs exactly $n_{m-1}$ accepted original Rho calls. At its Ready
boundaries the designated values are precisely $\rho^{n_i}t$ at these
identical epochs. Tied indices may designate the same boundary, including
$P$ when no construction is required. Every tuple with such a preparation
and pure-Rho tail satisfies these semantic conditions.

Proof. The beta-occurrence invariant holds initially. Reads, maintenance
and executed refusal preserve the source. An accepted Left/Right retains
the entire old source as one child. Each leaf's $\rho$ image contains
beta, so an accepted Rho also preserves the invariant. CAP's source-domain
invariant gives $\lambda(t)\le h$ at a completed boundary with guard $h$.
These prove necessity; no statement about the equality of full histories
has been made.

For the unrestricted image choose a numeral $h\ge\lambda(t)$; for the
fixed-capacity image use its stipulated $\lambda(t)\le h$. Select any
beta leaf in this supplied $t$. Starting at the actual $\beta$, build
the ancestors of that occurrence from the leaf
upwards. If the current subtree is the desired left child, issue
Right($v$) with the actual right sibling as context; if it is the right
child, issue Left($v$) with the actual left sibling. Supply that complete
finite sibling in the canonical prefix code. First complete Reserve($h$)
and Raise($h$) if $h>1$; omit them if $h=1$. CAP Theorems 5.2–5.3
preserve this same source occurrence and set $h=K$ without a Rho. Every
intermediate subtree has at most $\lambda(t)$ leaves, so every supplied
whole graft is accepted at this guard. If $h=1$, the only such $t$ is
beta and no graft is required. CAP Theorem 4.5, Lemmas 4.7 and 6.7,
ARC's actual outer01 entry and GENERAL Lemma 8.1 give the full finite
return after each call. This is a prescribed sequence of existing legal
frames; it does not replace the parked controller with a tree builder.

For the chronological assertion note
$\lambda(\rho u)=\lambda(u)+b(u)\ge\lambda(u)$, with $b(u)$ the
number of beta leaves. The stated final bound therefore bounds every
intermediate candidate, including $t$. Each of the next $n_{m-1}$ Rho
calls accepts and installs the declared iterate. Maintenance and grafts
have preserved accepted-Rho epoch zero, and subsequent accepted Rho
increments it once per call. The complete-return induction gives all
designated Ready boundaries. Conversely the stated prepared pure tail
has exactly these values, and its source-domain invariant gives the final
bound. $\square$

**Definition 13.3 (one-source class and its two label supports).** Let $I$
be any finite proposed-row/link input of Definition 1.2. Validate it before
using (NCE.4). Let $\Xi(\mathbf n,t,\mathbf x)$ be any additional finite
Boolean formula of Definition 10.1, with any further joint existential
tree variables. Its regular languages are supplied fixed descriptions.
For this one fixed numeral $h$, define

$$
\begin{aligned}
C_h(\mathbf n,t,\mathbf x)={}&
\operatorname{Chron}(\mathbf n)\land\Psi_I(\mathbf n,t,\mathbf x)
\land\Xi(\mathbf n,t,\mathbf x)\\
&\land\ t\in\mathsf{HasBeta}\land\rho^{n_{m-1}}t\in L_h,\\
E^+_h(\mathbf n)\ \Longleftrightarrow{}&
\exists t,\mathbf x\quad C_h(\mathbf n,t,\mathbf x)
                   \land\rho^{n_{m-1}+1}t\in L_h,\\
E^-_h(\mathbf n)\ \Longleftrightarrow{}&
\exists t,\mathbf x\quad C_h(\mathbf n,t,\mathbf x)
                   \land\rho^{n_{m-1}+1}t\notin L_h.
\end{aligned}
\tag{NCE.30}
$$

For malformed $I$ both supports are false, with the malformed indication
kept distinct from inconsistency. No reachedness guard, exterior leaf,
blocker, old-class negative or signed link is dropped. Class names are
local to their rows until linked. The same $t$, epoch tuple and entire
class valuations occur in all constraints.

**Theorem 13.4 (exact original-label possibility and uniqueness test).**
Both $E^+_h$ and $E^-_h$ are effectively Presburger, with simultaneous
native witnesses at each supported tuple. Their union is exactly the
support of $C_h$. Every witness has a source-value realization from the
same initialized $P$ by Theorem 13.2. At its last Ready, supply the next
actual outer01/Rho frame `0010`, seal/parse it, obtain the actual service
admission and complete ReadState. At this original source-body cut,
before generation, the lawful original completion protocol releases
accept exactly for the $E^+_h$ witnesses and executed refusal exactly
for the $E^-_h$ witnesses.

At a fixed tuple, neither support means the constrained source class is
unattainable; just one means this existing response label is unique on
that class; both mean that two actual alternative prefixes of the same
initialization give different labels of this admitted original experiment.
In the last case their original $Q$ responses are different. A unique
label proves no equality of complete responses or full-$Q$ behaviors.

Proof. Apply Theorem 10.2 to each formula in (NCE.30), including the
complemented capacity membership for the negative support. Proposition
2.2 identifies their rows and signed links with those of the one actual
source at the identical tuple. Theorem 13.2 realizes that source-value
tuple with its actual current guard and reserve. This realizes the
mathematical row truths; it does not assert that the constructed path
acquires the rows or publishes $\Xi$ as observer data.

CAP's source compiler tests the whole next candidate, whose value is
$\rho^{n_{m-1}+1}t$, against the actual $h$. ABT Convention 18.2,
AIF Definition 2.6 and SOURCECALL Lemma 2.3 give its already admitted
finite original completion through response release, before the changed
idle CTL. The prescribed enabled non-IN actions have their actual guards,
current owners, operands, labels and complete original joint successors.
Overlarge candidates are canonical executed refusals, not unexecuted
none. This proves the label assertion. The two complementary memberships
partition every candidate, giving the three cases of the decision test.

The completion protocol is used at its real admission point. Each
instance terminates finitely; no common all-source bound on its primitive
depth is asserted. For any two witnessing prefixes, their finite
completion traces give a finite original experiment distinguishing them:
use prescribed Advance and branch only on actual released responses. If
responses already differ sooner, they are already distinguished; if not,
continue through their finite completions to the differing release.
No private-state branch is needed. The original semantic protocol also
has its stated AIF admission. Equality of labels cannot reverse this
argument, because the response retains all other actual fields. $\square$

## 14. Source correspondence, authority, costs and remaining obligations

**Convention 14.1 (what the construction consumes).** The logical input
is a supplied finite formula, complete rows and declared regular predicates.
For actually acquired truthful records on the stated prepared pure-Rho
segment, their actual source belongs to (NCE.30) when its additional
predicates hold. To assert that this is the *entire* accessible-information
fiber still requires a two-sided acquisition/selection proof, including
all retained fields. No complete acquired request, context, snapshot,
archive or accessible distinction is removed to enlarge that fiber.
Theorem 13.2 supplies alternative source-value histories, not histories
with identical retained inputs or identical physical records.

This distinction is substantive in [NASF, Definitions 1.2–1.4 and Theorem
3.4][NCE-NASF]: one returning adaptive program has its entire accessible
output and branch-sensitive history fiber. Its exact representation is
in general a countable family of finite constraints. NASF Theorem 6.2
and Corollary 6.3 concern the undecidable fiber of one such program;
Theorem 10.2 does not make that countable family one finite formula.
NRF Theorem 6.6 retains every original source for its regular-selector
producer, with a separate invocation/validation/Return correspondence.
The arbitrary shared signed epoch comparisons here do not instantiate
that producer or its complete handoff in $G_{\mathrm{gc}}$.

**Convention 14.2 (literal implementation and evidence interfaces).** The
native interpretation and public/private proof suppliers retain these
exact scopes; reading them supplies documentary correspondence, not a new
kernel certificate.

| Source | Interface used and boundary |
| --- | --- |
| ABC Theorems 2.2–2.3; NCE Sections 2–4; SFP Sections 2–4 | Normal-code identities, same-source row compilation, scalar/block alignment and source-preserving arbitrary-shape coordinates are reused. Constant residual replacement is not applied to memberships. |
| NRF Definition 4.1 and Sections 6–7 | Primitive-state periodicity and finite regular-domain methods are suppliers; their fixed selected-row producer is not the present arbitrary signed cross-epoch input. |
| [NativeUnificationCore][NCE-CORE], namespace `NativeTermUnification` | `Source = FreeMagma Bool`, `Term X = FreeMagma (Bool ⊕ X)`, `evaluate` and the literal constructor encoding. There is no interpreted free-power symbol in this Lean term signature. |
| [NativeGroundSolutionSpace][NCE-GROUND] and its [Scribe][NCE-GROUND-S] | `solutionEquiv` retains the full original assignment; `constrainedEquiv` pulls back an already supplied arbitrary predicate, and does not decide it. |
| [NativeHistoryCells][CELL], its [Scribe][CELL-S]; [NativeSymbolicRecutting][NCE-RECUT] | Private `syntax_iff_ground`, public `cell_feasibility_exact`/`historyCellEquiv` and `symbolic_recut_exact` keep complete old-class negatives and actual fixed-history/depth scopes. They are not replaced by state equality. |
| [NativeWholeRowPlan][NCE-PLAN] | Private `ground_action_value` actually consumes `parameterization.ground_exact`; public `pair_plan_correct` consumes `native_complete` in the failed-unification branch. These are existing consumers, not an installed evaluator of (NCE.23). |
| CAP Sections 1, 4–6; ARC Definitions 4.1, 5.2, 9.1; GENERAL Lemma 8.1 | Existing seven-label ingress, current source16/$\phi_K$, maintenance, source semantics and complete paid returns establish Theorems 13.2–13.4. AIF/SOURCECALL establish only the indicated original-row completion domain. |

**Convention 14.3 (resources and the four independent expressions).**
The finite decision construction can enlarge Boolean branches, unifiers,
automaton products, guard regions and Presburger descriptions. No complexity
bound, installed solver or cheap witness expansion is asserted. Output
expansion has its actual native size as in (NCE.21). A mathematical
membership predicate is not a new source instruction.

Every physical preparation and test uses the existing producer/current
service token, actual source binding, code, scratch and channels. Complete
contexts and frames are actually supplied at their prescribed INs. All
Base/seek/Resolve work, ingress, generation, source writes, guards, fences,
counters, row/index construction, copies, receiver seals/checks, ACKs,
owner transfers, InnerReturn and CaptureCAP remain paid and retained on
their own run. If its literal primitive suffix has $N$ rows, it has $N$
receipts, $N$ ticks and $2N$ fee units; the earlier entrance bill stays
separate. Non-meter material and complete marked receipts keep their
actual sizes and contents. Leaf number, accepted-Rho epoch, semantic
source/event counters and primitive ordinal are different coordinates.
No cross-run cost equality, monotonicity or zero-cost read follows.

The source tree and its code shape are not physical storage support $S$,
terminal boundary $B$, actual occurrence-order $T$, or joint retained and
permission-bearing $M_J$. A mathematical joint valuation is not actor
memory. The original client remains parked; neither a supplied context
nor a historical permission installs an adaptive controller or current
read right. Complete original successors remain task outputs, not actor
inspection rights. Theorem 13.4 uses an included original released label;
it does not decide inclusion of annex fields or equate full responses.

**Problem 14.4 (remaining recovery bridge).** A practical use still needs
actual lawful acquisition of the required complete records, comparisons
and membership evidence, a proved exact selection-aware fiber, current
access to those operands, an installed consumer and paid handoff/return.
The regular membership theorem alone authenticates none of these.
GENERAL's existing paid historical four-view conversions and source-only
original-response inverses remain suppliers at their exact domains.

The complete original-$Q$ correspondence, synchronized-mate and equal-weight
complete-response comparisons, independent successful mixed inputs and
growth, changed-return/annex admission, arbitrary old targets, and the
raw/bootstrap/preacquisition/unfinished/fault/final00/absorbing-terminal
domains retain their existing obligations. All-domain mutual recovery of
the four independently defined expressions and currently callable use
remain the full programme. Theorems 10.2 and 13.4 supply a finite logical
extension and an actual original-label consumer, not that completion.

**References 14.5 (mathematical attribution and fixed capacity).** The
common-shape rank automaton, its exact assembly and the source-class
application are `repo-derived` ordinary proofs. No new Lean verification
or worldwide-originality claim is made. Comon–Delor, *Equational Formulas
with Membership Constraints*, Information and Computation 112(2), 167–216,
DOI [10.1006/inco.1994.1056][NCE-CD-DOI], author manuscript Lemma 1
(pp. 7–8), Theorem 4 and Corollary 2 (p. 33) [NCE-CD], is
`literature-attested` only for the ordinary admissible $c/f$ shape problem
after the proved native elimination. No arbitrary homomorphism extension,
HOM image-language comparison or TABG flat-theory enlargement is assumed.
Ginsburg–Spanier Theorems 1.2–1.3 [GS] supply the final Presburger decision
and semilinear conversion. The pinned mathlib interface
`presburger.definable_iff_isSemilinearSet` in
`Mathlib/ModelTheory/Arithmetic/Presburger/Definability.lean` has that
arithmetic scope, not the new native elimination.

The capacity quantifiers are $\forall h\ge1$ supplied as a numeral,
$\exists$ a constructed $L_h$ automaton and formulas $E_h^\pm$.
Automaton size and formula syntax may depend on $h$. This is different
from one finite formula with fixed automata and free numeric capacity
$h$. [ABT, Sections 24–26][NCE-ABT] gives the attained original-response
boundary for that uniform language. Neither result turns semantic
source replacement into actual acquired or callable memory.

[NCE-SFP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SOURCE_FIBER_PARAMETRIZATION.md
[NCE-NRF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REGULAR_FRONTIER_SELECTION.md
[NCE-NASF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ADAPTIVE_SELECTION_FIBERS.md
[NCE-ABT]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md
[NCE-CORE]: ../../../D5/S0/Rewriting/NativeUnificationCore.lean
[NCE-GROUND]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.lean
[NCE-GROUND-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.scribe.cs
[NCE-RECUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[NCE-PLAN]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.lean
[NCE-CD]: https://lsv.ens-paris-saclay.fr/~comon/ftp.articles/membership.ps
[NCE-CD-DOI]: https://doi.org/10.1006/inco.1994.1056

## 追加锚（本行以下为增补区）
