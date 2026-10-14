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
