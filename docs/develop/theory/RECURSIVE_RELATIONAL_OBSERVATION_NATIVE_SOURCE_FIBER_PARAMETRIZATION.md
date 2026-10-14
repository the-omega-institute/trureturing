# Every original source in a signed unknown-epoch native fiber

This volume gives a finite description by arbitrary finite residual shapes,
selected mismatch leaves, and explicitly solved affine rank coordinates.
The arithmetic dimension depends on the supplied shapes. Every decoded
point is an original source at its specified epochs, and every original
realization has effective coordinates decoding to that identical point.
The construction resolves native negatives into structural disagreements
or scalar inequalities; it retains neither an unevaluated native negative
list nor a native common-source predicate as its admission test.

The arguments are ordinary mathematical proofs, not new Lean kernel
evidence. The native construction is `repo-derived`. Its exact suppliers and the
restricted uses of primary literature are specified below. The persistent
RRO objective of recovering space, time, boundary and memory from a minimal
relational structure remains broader than this finite representation.

## 1. The native domain and the supplied exact problem

**Definition 1.1 (sources, epochs and complete rows).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle u,v\rangle&=\langle\rho u,\rho v\rangle.
\end{aligned}
\tag{SFP.1}
$$

All trees are nonempty, finite, full and ordered. Addresses are finite
words in $L,R$, with root $\varepsilon$. A subtree is defined only at a
reached address. For a finite prefix-free cut $P$, the complete row
$R_P(u)$ retains the entire literal exterior, an addressed hole at each
reached cut, and the entire equality partition of the hole values.
Every pair of different classes asserts disequality. Every unreached
cut retains its concrete blocking leaf at a strict prefix. A root cut
has one hole; an empty cut retains the whole tree.

Use exactly [NCE, Definition 1.2][NCE]. An input $I$ has $m\ge1$ proposed
complete rows $(P_i,R_i)$ and a finite list of signed links
$((i,p),(j,q),\epsilon)$ with $\epsilon\in\{=,\ne\}$. Validate finite
ordered full exteriors, prefix-freeness, the address alphabet, every
hole's own address and single occurrence, every blocked request, the full equivalence relation
on precisely the holes, row indices and signs. Every link endpoint must
be a reached hole of its proposed row. A failed validation gives the
empty representation with a malformed-input indication. Inconsistency
of a well-formed input instead means that its represented domain is empty.
Neither sign assigns a default subtree to an absent endpoint.

**Definition 1.2 (the entire common-source fiber).** Write

$$
\begin{aligned}
\mathscr H_I=\{(t,\mathbf n):\ &t\in\mathcal T,\quad
\mathbf n\in\mathbb N^m,\quad 0=n_0\le\cdots\le n_{m-1},\\
&R_{P_i}(\rho^{n_i}t)=R_i\quad(i<m),\\
&(\rho^{n_i}t)|_p\ \epsilon\ (\rho^{n_j}t)|_q
 \quad(((i,p),(j,q),\epsilon)\in\Lambda)\}.
\end{aligned}
\tag{SFP.2}
$$

The link line includes both reachedness requirements. The same $t$ occurs
everywhere. No upper bound on epochs, source size, source depth or atomic
age is imposed. Ties, repeated endpoints, reflexive signs, zero holes,
empty link lists and empty fibers are included.

For a validated row write its exterior as $C_i$, its holes as $H_i$,
and its classes as $\mathcal B_i$. Use one variable $x_{i,b}$ for every
class, shared at all of that class's occurrences, and set

$$
\begin{aligned}
W_i(\mathbf x)&=C_i[(x_{i,[p]})_{p\in H_i}],\\
\Psi_I(\mathbf n,t,\mathbf x)&=
\bigwedge_{i<m}\rho^{n_i}t=W_i(\mathbf x)
\ \land\ \bigwedge_i\bigwedge_{b\ne c}x_{i,b}\ne x_{i,c}
\ \land\ \bigwedge_{\Lambda}x_{i,[p]}\ \epsilon\ x_{j,[q]}.
\end{aligned}
\tag{SFP.3}
$$

[NCE, Proposition 2.2][NCE] supplies the equivalence between (SFP.2)
and the existence of the class valuation in (SFP.3), at the same original
$t$ and the same chronological tuple. That valuation is unique once
$(t,\mathbf n)$ is fixed. Equation (SFP.3) is the input to the construction,
not its proposed output representation.

**Convention 1.3 (what is already supplied).** [ABC, Theorems 2.2–2.3][ABC]
supply mutually inverse effective maps $B:\mathcal T\to\mathcal N$ and
$E:\mathcal N\to\mathcal T$. A normal code is a finite ordered term over
$F$ and natural primitive ranks $[r]$, with every primitive cherry
$F([r+1],[r])$ forbidden. Put $T_r=\rho^r\alpha$. Then

$$
\begin{aligned}
E([r])&=T_r,&E(F(X,Y))&=\langle E(X),E(Y)\rangle,\\
J(X,Y)&=
\begin{cases}[r+2],&X=[r+1],\ Y=[r],\\F(X,Y),&\text{otherwise},\end{cases}\\
B(\rho^a u)&=\tau_aB(u),&
E(J(X,Y))&=\langle E(X),E(Y)\rangle.
\end{aligned}
\tag{SFP.4}
$$

Here $a\in\mathbb N$ and $\tau_a$ adds $a$ to every rank. Its image
consists exactly of normal codes with every rank at least $a$; subtraction
on that image is its inverse. We never use a negative native iterate.

[NSF, Sections 2–3][NSF] supply positive flattening, free-shape unification
and the remaining scalar and whole-block offset equations. Its Section 4
replaces residual shapes and ranks for existential witnesses. [NCE,
Theorems 4.2 and 5.1][NCE] supply affine existential epoch support and
one replaceable witness at each accepted tuple. NCE Corollary 5.3 and
Theorem 6.2 already decide source-value and lag uniqueness. Those decisions
are not new consequences claimed here.

[NIC, Theorems 3.2–3.3][NIC] supply all-source positive fixed-shift images
and native signed pullbacks. [PDC, Theorem 5.2][PDC] supplies injective
all-source charts and its Theorem 6.2 supplies original-prefix
correspondence. PDC's exact output grammar is

$$
A::=g\mid T_{r_j+c}\mid\rho^a(z_l)\mid\langle A,A\rangle,
\qquad a,c\in\mathbb N\text{ fixed},
\tag{SFP.5}
$$

with retained whole native negatives on the residual native parameters.
Its $r_j$ are scalar coordinates; they do not make the residual exponent
$a$ variable. The increment here is a source-preserving representation
with affine unknown epochs and fully resolved negatives, at the price
of explicit arbitrary shapes and a shape-dependent arithmetic dimension.
No claim of injectivity of all coordinates, or of a uniform prefix
modulus for them, is needed.

## 2. The output language before any completeness claim

**Definition 2.1 (shape and arithmetic parameters).** A ground shape is
an arbitrary nonempty finite ordered full tree

$$
K::=c\mid f(K,K).
\tag{SFP.6}
$$

Its positions, leaf positions and primitive cherries are finite sets of
$L/R$ words obtained by traversal. A primitive cherry is a node both of
whose children are leaves. Equality of two supplied ground shapes is
literal ordered-tree equality. If unequal, traversal produces an address
where both nodes exist and one is $c$ and the other is $f$; choose the first
such address in a fixed traversal order. This uses no native expansion.

A finite shape template is a term over $c,f,w_1,\ldots,w_s$. Substitution
of a tuple $\mathbf K$ of ground shapes gives a ground shape. Distinct
$w_j$ may receive the same shape. Repeated occurrences of $w_j$ share
only that shape: they do not, merely for this reason, share leaf labels.
An affine form in epoch parameters $\mathbf n$ has integer coefficients.
All scalar coordinates in the final representation are natural numbers.

**Definition 2.2 (finite leaf-arithmetic scheme).** A scheme consists of
finitely many names $v$, including designated output names, one finite
shape template $S_v$ for every name, a finite affine parameter guard,
and finite lists of the following edge instructions:

1. $\operatorname{Align}(v,w,a)$, with identical shape templates, creates
   $r_{v,p}-r_{w,p}=a(\mathbf n)$ at every corresponding leaf;
2. $\operatorname{Pair}(v,l,r)$, with $S_v=f(S_l,S_r)$, creates
   $r_{v,Lp}-r_{l,p}=0$ and $r_{v,Rq}-r_{r,q}=0$ at every child leaf;
3. $\operatorname{Anchor}(v,k)$, with $S_v=c$, creates
   $r_{v,\varepsilon}-r_o=k$, where $r_o=0$ and $k$ is a fixed integer.

The scheme also has a finite list of pairs of names required different.
That list is an instruction for generating mismatch coordinates, not a
native disequality predicate in the final domain. Normality is enforced
by the universal local instruction in Definition 2.3, not by an oracle
for normal native trees.

Given $\mathbf K$, set $H_v=S_v[\mathbf K]$. The temporary rank-vertex
set is the disjoint union

$$
V(\mathbf K)=\{o\}\ \sqcup\
\coprod_v\{(v,p):p\in\operatorname{Leaves}(H_v)\}.
\tag{SFP.7}
$$

Reuse of a name reuses these very vertices. Different names and different
positions initially have different vertices, even when their shapes are
identical. Only listed positive edge instructions relate their ranks.
These instructions generate a finite affine-labelled equality graph.
They generate neither native trees nor a search through possible sources.

**Definition 2.3 (resolved negative and normality instructions).** For
each negative pair $(v,w)$, compare the supplied $H_v,H_w$.
If unequal, store the structural disagreement address computed in
Definition 2.1; no scalar inequality is required for this pair.
If equal, a mismatch coordinate $\eta_{vw}$ is any leaf of this common
shape, and generate

$$
r_{v,\eta_{vw}}-r_{w,\eta_{vw}}\ne0.
\tag{SFP.8}
$$

There are finitely many choices for a supplied shape tuple, but no
uniform bound on the length of a chosen leaf address. All negative
pairs choose their witnesses jointly. Let $M(\mathbf K)$ denote this
finite product of choices, with the unique empty tuple when there are
no negative pairs. Membership in $M(\mathbf K)$ is decided solely by
shape traversal and leaf-address membership.

For every primitive cherry at address $q$ in every $H_v$, generate

$$
r_{v,qL}-r_{v,qR}\ne1.
\tag{SFP.9}
$$

This includes cherries entirely inside residual shapes and cherries
formed where a primitive residual meets another child. No fixed
nonleaf-marker convention is used. Let $D(\mathbf K,\boldsymbol\eta)$
be the resulting finite list of forbidden rank differences, from both
(SFP.8) and (SFP.9).

**Definition 2.4 (solved scalar coordinates).** Choose a deterministic
spanning forest of the equality graph, ignoring the numerical values
of its affine labels. Root the component containing $o$ at $o$ and every
other component at one of its rank vertices. Set its root potential to
zero and propagate signs along the forest, obtaining affine forms
$\delta_u(\mathbf n)$ with
$\delta_u-\delta_v=a_e$ for each forest edge
$r_u-r_v=a_e$. Let $C(u)$ denote a component. Use a natural base $b_C$
for each component other than $C(o)$, and abbreviate $b_{C(o)}=0$.
The entire arithmetic guard is

$$
\begin{aligned}
A(\mathbf n,\mathbf b):\quad &G(\mathbf n),\\
&\delta_u(\mathbf n)-\delta_v(\mathbf n)=a_e(\mathbf n)
                 &&\text{for every equality edge }e=(u,v),\\
&b_{C(u)}+\delta_u(\mathbf n)\ge0
                 &&\text{for every rank vertex }u,\\
&b_{C(u)}-b_{C(v)}+\delta_u(\mathbf n)-\delta_v(\mathbf n)\ne d
                 &&\text{for every }(u,v,d)\in D.
\end{aligned}
\tag{SFP.10}
$$

Both endpoints of an equality edge lie in the same component. Thus its
bases cancel in the second line. In particular a cycle with symbolic
sum $n_i-n_j$ imposes $n_i=n_j$; it is not discarded for having a
nonzero formal label. The zero vertex has potential zero and fixed
rank zero. Every other rank is reconstructed by

$$
r_u=b_{C(u)}+\delta_u(\mathbf n).
\tag{SFP.11}
$$

For fixed $\mathbf K,\boldsymbol\eta$, (SFP.10) is an explicitly
constructed finite quantifier-free Presburger condition. It contains
no equality of native trees, no $\rho$, no source variable, no recursive
normality predicate and no unresolved whole-block comparison.

**Definition 2.5 (admission and decoding).** A finite output description
is a finite list of schemes. Its coordinates are

$$
a=(b,\mathbf K,\boldsymbol\eta,\mathbf n,\mathbf b),
\qquad
\boldsymbol\eta\in M_b(\mathbf K),\quad
A_{b,\mathbf K,\boldsymbol\eta}(\mathbf n,\mathbf b).
\tag{SFP.12}
$$

Here $b$ is a scheme index, distinct from the component bases $b_C$.
Admission first checks the finite shapes and mismatch addresses, constructs
the graph and (SFP.10), and evaluates its affine relations. It never
calls the original predicate (SFP.2) or (SFP.3).

To decode, label every leaf of $H_v$ by (SFP.11), replace $c$ with that
primitive $[r_u]$ and $f$ with $F$, obtaining $X_v$. Expand designated
outputs by $E$ and retain the supplied $\mathbf n$ unchanged. The local
inequalities (SFP.9) make each $X_v$ normal. Expansion is a terminating
operation on finite supplied ranks and shapes.

The shape tuple is unrestricted in (SFP.6); admission can subsequently
exclude a shape tuple through an empty arithmetic fiber. There is no
fixed-dimensional semilinear claim about the whole coordinate space.
For a fixed shape tuple there are finitely many mismatch choices and
finite-dimensional arithmetic fibers; their dimensions and number can
grow with that tuple. The finite description precedes both the residual
shape assignments and all numerical epochs. Its bounded traversals
are specified above, so it is more specific than an arbitrary program
that tests a source predicate.

## 3. Construction from affine native syntax

**Definition 3.1 (the intermediate input language).** Consider finitely
many declared variables $x_1,\ldots,x_r$ ranging over $\mathcal T$, a
natural parameter tuple $\mathbf n$, a finite Boolean affine guard
$G(\mathbf n)$, and a finite Boolean combination $\Phi$ of equalities
between expressions

$$
A::=\alpha\mid\beta\mid x_j\mid\langle A,A\rangle
                   \mid\rho^{a(\mathbf n)}A.
\tag{SFP.13}
$$

Each exponent is a specified integer-affine form; $G$ requires it to
be nonnegative. Constants that are finite native trees abbreviate their
literal syntax. All declared variables remain outputs, including unused
ones. There are no infinite or rational trees, variable-address operations,
arbitrary morphisms, products of epoch variables or tree-quantifier
alternations in this language.

**Construction 3.2 (finite branches before parameter evaluation).**
Distribute $\Phi$ into finitely many conjunctions. Give every declared
variable and every subexpression a code name, sharing all occurrences
of any one variable. All subexpression definitions remain positive,
including those beneath a negative comparison. Use (SFP.4) to obtain
primitive definitions $X_v=[0],[1]$, shifts
$X_v=\tau_{a(\mathbf n)}X_w$, and smart pairings
$X_v=J(X_l,X_r)$, together with the signed comparisons.

For each smart pairing make the two exhaustive choices

$$
\begin{array}{ll}
\text{collapse:}&s_l=s_r=s_v=c,\quad
       r_l-r_r=1,\quad r_v-r_r=2,\\
\text{ordinary:}&X_v=F(X_l,X_r).
\end{array}
\tag{SFP.14}
$$

The primitive ranks of all three names remain natural. No new independent
collapse scalar is needed: the rank of the existing right name supplies
it. The ordinary case requires normality of its output like every other
name, thereby excluding the collapse case.

Erase ranks. Primitive definitions force shape $c$, shifts and positive
equalities equate shapes, and ordinary pairing gives
$s_v=f(s_l,s_r)$. Solve these finite equations over the free signature
$c,f$ by an idempotent most general unifier, with the finite-tree occurs
check. A failure discards the branch. A success supplies finite terms
$S_v$ in residual shape variables $w_1,\ldots,w_s$ and the complete
factorization of all finite shape solutions. Keep unused names as well.
This is precisely the free-shape step of NSF Section 3; the classical
unification supplier is Baader–Snyder §2.2.4, Lemma 2.2, Corollary 2.3, Lemma 2.4 and
Theorems 2.5–2.6 [BS]. It is applied after native collapse splitting,
never to $\rho$ as a free unary constructor.

For each successful branch generate the finite scheme:
primitive definitions give anchors; shifts and positive equalities give
alignment instructions with their actual affine labels; collapse gives
its two primitive alignments; ordinary pairing gives a pair instruction.
Keep every original negative pair for Definition 2.3. No shape inequality
is asserted merely because two symbolic templates differ. No equality
of ranks is added merely because two shapes happen to coincide.

**Lemma 3.3 (all normal assignments on a supplied residual shape).**
For any successful branch, any supplied $\mathbf K$ and any guarded
numerical $\mathbf n$, the decoded normal assignments satisfying all
branch definitions and signed comparisons are exactly the assignments
obtained from (SFP.12). This correspondence retains every rank at every
leaf of every name.

Proof. All positive shape equations hold after substituting $\mathbf K$
into the unifier. On equal ground shapes, equality of codes is exactly
equality of the corresponding ranks. A uniform translation adds its
affine value at each such leaf. For ordinary pairing, the output's
left and right leaf addresses are respectively $Lp$ and $Rq$; the
pair instruction therefore expresses exactly its defining code equation.
Anchors and collapse alignments have their literal meanings. Reassembling
these comparisons proves that the graph equations are equivalent to all
positive branch definitions and equalities.

A finite code on $H_v$ is normal exactly when its labels are natural and
none of its primitive cherries has left rank one greater than right.
These are precisely all the nonnegativity conditions and (SFP.9).
This check includes every node after substitution. In particular a
residual shape $c$ can create a new cherry at an insertion boundary,
and that cherry is checked. No assertion about the nonprimitive root
of a residual was assumed.
For example, dropping these checks would let the different ambient
shapes of $F([1],[0])$ and $[2]$ certify a false native disequality:
both expand to $T_2$. Their use in the negative argument below therefore
depends on all-name normality.

For two normal codes on different ground shapes, code equality is
impossible; injectivity of $E$ on $\mathcal N$ makes their native
expansions different as well. For two codes on the same ground shape,
inequality holds exactly when some corresponding leaf labels differ.
The shape is finite and nonempty, so an unequal pair admits one of the
witnesses (SFP.8). Conversely such a witness establishes inequality.
Choose these leaves independently as certificates but evaluate all of
them on the same shared rank assignment. A negative comparison of a
name with itself necessarily gives $r-r\ne0$ and has no solution.

It remains to solve the graph without changing any solutions. Following
forest edges in an actual rank assignment gives (SFP.11), with $b_C$
its actual root rank. These bases are natural, and the anchored base is
zero. Every remaining equality is exactly the second line of (SFP.10),
and every required disequality becomes its last line. Hence actual
ranks yield admitted bases without alteration.

Conversely, (SFP.10) and (SFP.11) reconstruct every graph edge: the two
bases cancel and its potential equation supplies the required difference.
They reconstruct natural labels and all selected forbidden differences.
The previous paragraphs then reconstruct every normal named code and
all signed branch constraints. Taking the rank of a forest root is an
inverse to (SFP.11) for each fixed shape and witness selection. There is
no replacement by a constant field or a different shape. $\square$

**Proposition 3.4 (shape coincidence does not merge values).** The
construction is valid even when different residual variables receive
the same ground shape, when multiple occurrences of one shape variable
have independent rank fields, and when a negative first differs
arbitrarily deep inside a residual.

Proof. The vertex names in (SFP.7) contain both the code name and the
leaf address. Ground shape coincidence adds no edges to the positive
graph. Its only effect on a negative is to require the leaf-witness
alternative in Definition 2.3 instead of the shape-disagreement
alternative. Lemma 3.3 compares every such leaf with its actual shared
rank and allows all depths in the supplied finite shapes.

For example $F([0],[0])$ and $F([0],[2])$ are normal and share a shape,
but their rank differences are not a constant function. They cannot be
identified by a shape equation. NIC Lemma 2.4 derives connectivity of
residual sorts from the provenance of its original positive shape
equations. We need no such connectivity assumption, and use no such
lemma after introducing structural tests for negatives. The forest
always retains all of its actual components. $\square$

## 4. Exact forward decoding and reverse extraction

**Theorem 4.1 (all-source affine native representation).** From any
finite input of Definition 3.1 one can construct a finite list of schemes
of Definition 2.2, independently of all numerical parameters, such that

$$
\{(\mathbf x,\mathbf n):G(\mathbf n)\land\Phi(\mathbf n,\mathbf x)\}
=
\{\operatorname{Decode}(a):a\text{ satisfies (SFP.12)}\}.
\tag{SFP.15}
$$

Every admitted coordinate decodes to its designated original native
values at its identical parameter tuple. From any supplied solution
$(\mathbf x,\mathbf n)$ one can effectively extract admitted coordinates
$a$ with $\operatorname{Decode}(a)=(\mathbf x,\mathbf n)$.
No search through source trees, fixed shape list, size bound or numerical
epoch bound is used. Coordinates need not be unique.

Proof. Construction 3.2 is finite: Boolean branching and smart-pairing
choices range over a finite expression graph; each free-shape unification
terminates; successful unifiers and edge-instruction lists are finite.
These operations inspect syntax and affine forms, not numerical epochs.
The generic operations of Section 2 are fixed finite recursive algorithms
on the subsequently supplied finite shape tuple. This constructs the
claimed finite description before either kind of parameter is supplied.

For soundness, let $a$ be admitted. Lemma 3.3 makes every named code
normal and supplies every branch definition and comparison. A primitive
definition expands to the correct native constant. A shift expands to
its actual natural iterate by ABC. In a collapse branch the right
primitive rank is a natural $r$ and the other ranks are $r+1,r+2$, so
(SFP.4) verifies exactly that smart pairing. In an ordinary branch the
normality of the output excludes a primitive collapsing cherry. Thus
induction up the original expression graph identifies each decoded name
with its native subexpression at the decoded original variable values.
This induction reuses one value at every repeated occurrence.
The positive and negative atoms of the chosen conjunction hold on those
same values, so $\Phi$ holds. The retained guard is $G$, and decoding
never changes $\mathbf n$.

For completeness, evaluate every named native subexpression in the given
actual solution and apply $B$ to all of them. Choose a true Boolean
conjunction and each actual smart-pairing case. These choices give a
solution of the finite positive shape equations. Their unifier therefore
succeeds. Choose residual variables among the remaining original shape
variables of the idempotent unifier; read their actual ground values.
The factorization identity gives

$$
\operatorname{sh}(B(\text{value of name }v))=S_v[\mathbf K]
\quad\text{for every }v.
\tag{SFP.16}
$$

This is an effective restriction and substitution on a finite unifier;
it neither enumerates shapes nor replaces any actual shape. Retain the
actual rank at every vertex in (SFP.7). For each negative pair with equal
ground shapes, take its first differing leaf; different shapes supply
the structural certificate. Such witnesses exist because the actual
normal codes are unequal. All cherries are normal in these very codes.

Take $b_C$ to be the actual rank at the chosen root of each free equality
component. Lemma 3.3 proves admission and reconstructs exactly every
original rank. Consequently all decoded codes are the originally
computed $B$ codes, not just codes of the same shape. ABC's identity
$E(B(x_j))=x_j$ recovers each original variable unchanged. Extraction
uses finite expression evaluation, coding, shape restriction, finite
traversals and integer arithmetic, and terminates on each supplied
finite solution. Repeated possible mismatch witnesses or Boolean
branches explain why no uniqueness claim for coordinates is made.
$\square$

**Corollary 4.2 (the complete NCE fiber).** For every input of Definition
1.1 there is a finite description as in Section 2 and a decoding map
$D_I$ whose image is exactly $\mathscr H_I$. There is an effective
extraction map on supplied members of $\mathscr H_I$ with

$$
D_I(\operatorname{Extract}_I(t,\mathbf n))=(t,\mathbf n).
\tag{SFP.17}
$$

Proof. Malformed input has the empty description. On valid input apply
Theorem 4.1 to (SFP.3), keeping $t$ and every class variable as designated
variables and using chronology as the guard. Project the decoded output
to its one $t$ and its original epoch tuple. NCE Proposition 2.2 makes
soundness exactly membership in (SFP.2).

For reverse extraction, take the actual subtree at a representative
reached hole of every class in every actual $\rho^{n_i}t$. The NCE
supplier gives its unique joint valuation satisfying (SFP.3). Apply the
extraction in Theorem 4.1 to that valuation. It retains precisely $t$
and $\mathbf n$, proving (SFP.17). Entire iterate equations handle
later-born endpoints, rather than transporting them backward to an
originally nonexistent subtree. $\square$

**Proposition 4.3 (the domain includes degenerate and conflicting data).**
Corollary 4.2 retains empty, root, mixed and blocked cuts, rows with no
holes, ties, repeated endpoints, every old-class disequality and
inconsistent input.

Proof. A zero-hole row gives a ground $W_i$ and the unique empty class
valuation. An empty cut has that meaning; a root cut instead supplies
one unrestricted class variable. Mixed and blocked rows keep all
concrete constructors and blockers in $W_i$. Prefix-free validated
exteriors cannot lose those blockers when filled. Every distinct class
pair enters the negative list, even when neither class is linked to
another row. Class labels printed in different rows are different
variables unless a constraint relates them.

Non-strict chronology includes ties. At a tie two rows constrain the
same iterate of the same source, so incompatible rows yield no admitted
coordinates. A reflexive equality contributes tautological edges; a
reflexive negative gives the impossible condition in Lemma 3.3.
Contradictory signs on a repeated pair force a forbidden zero difference.
The empty link list contributes no extra instructions. Well-formed
inconsistency can appear as failed shape unification or an empty
arithmetic fiber, without requiring an inhabitation promise.

For a concrete born-hole case, take the first cut $\{LL\}$ with exterior
$\alpha$ and zero holes, and the later cut $\{L,R\}$ with two distinct
classes and no links. The exact histories are $(\alpha,(0,n))$ for
$n\ge2$: $T_n=\langle T_{n-1},T_{n-2}\rangle$ has distinct children
for exactly these $n$. Both later holes were absent originally. A link
purporting to use the first row's $LL$ is malformed and cannot be made
valid by assigning it a default value. $\square$

## 5. Refinement without replacing the original source

**Definition 5.1 (coordinate refinement by further retained signs).**
Let $I^+$ add a finite list of signed links between already reached holes
of the same proposed rows, retaining all old data. On a scheme of $I$
and a supplied shape tuple, locate the existing names of the compared
class values. For a new positive comparison, reject that shape tuple if
the ground shapes differ; otherwise add all corresponding zero-offset
leaf edges. For a new negative, apply Definition 2.3 and retain all
old mismatch witnesses. Recompute the forest and (SFP.10).

This operation uses finite shape comparison and affine arithmetic only.
It does not require expanding a native tree. A new positive comparison
can connect previously separate rank components; it never identifies
ranks merely from shape equality without those new code-equality edges.
This is an update on a supplied shape tuple. For a new finite scheme
list before shape assignment, apply Corollary 4.2 to $I^+$; the
per-shape update does not silently enlarge the scheme instruction grammar.

**Theorem 5.2 (exact retained-data refinement).** The operation of
Definition 5.1 preserves exactly all original histories of $I^+$,
at their original epoch tuples. On every supplied old shape tuple it
has effective coordinate maps in both directions between compatible
old assignments with new mismatch witnesses and refined assignments.
They preserve every named code, hence every original source and all
old memory relations.

Proof. Retain the old rank vertices. A new positive is equivalent to
shape equality together with equality of all corresponding ranks.
A new negative is equivalent to exactly the structural or selected-leaf
alternative of Lemma 3.3. Therefore the enlarged graph and forbidden
list characterize precisely the compatible old rank assignments.

Given compatible old coordinates, first reconstruct their ranks by
(SFP.11), choose any required new unequal leaves, and take their values
at the new forest roots as the new bases. These bases satisfy the
refined arithmetic guard. Conversely, from refined bases reconstruct
all ranks and read them at the old forest roots; the old guard holds
because every old constraint was retained. The two operations preserve
all ranks, with the chosen negative witnesses retained in the
correspondence. Lemma 3.3 and Corollary 4.2 give the asserted source and
epoch correspondence. This proof covers accidental equality of supplied
residual shapes and every resulting merger of components. $\square$

The theorem gives an exact data-preserving update of the represented
alternatives. Nonemptiness of an arbitrary unspecified shape fiber is
not decided by trying shapes. For any fixed supplied shape tuple,
existence of its arithmetic coordinates is decidable by ordinary
Presburger arithmetic; this includes any finite set of such shapes.
Global signed-existence and opposite-sign existential queries already
have the NCE supplier. No new global inclusion, equality or arbitrary
tree-quantifier decision is inferred from this refinement operation.

**Proposition 5.3 (why a single witness section cannot perform this task).**
If a history fiber at one epoch tuple contains two different sources,
retaining only one source witness at that tuple cannot preserve every
later complete-row refinement of that fiber.

Proof. Let the retained witness be $t_*$ and choose another actual
source $t\ne t_*$. Append an empty-cut row with literal exterior
$\rho^{n_{m-1}}t$, at a new last epoch tied to $n_{m-1}$. This is a
finite permitted row. The same $(t,\mathbf n)$, with its repeated final
epoch, realizes the refinement. The witness $t_*$ does not, because
$\rho^{n_{m-1}}$ is injective by ABC. Thus the refinement is nonempty
and discards the retained witness. Corollary 4.2 recompiles the extended
finite record while retaining this original $t$. This is a failure of
witness replacement as a memory representation, not a new existential
undecidability result or a new decision procedure. $\square$

## 6. A linked-row family with exact residual and lag memory

**Definition 6.1 (the two-row linked family).** Let both cuts be
$P_0=P_1=\{L,R\}$. Each proposed row is an ordered root pair of holes
with two distinct classes. Use epochs $(0,d)$ and retain the links

$$
(0,R)=(1,L),\qquad (0,L)\ne(1,R).
\tag{SFP.18}
$$

The second link is included to specify a full signed example, even
though the positive link and within-row negatives will force it.

**Proposition 6.2 (all residuals and their exact rank coordinates).**
The entire fiber of Definition 6.1 is

$$
\{(\langle u,\rho^d u\rangle,(0,d)):
                     u\in\mathcal T,\ d\ge1\}.
\tag{SFP.19}
$$

One exact source representation uses any ground shape $K$, one natural
label $a_p$ for every leaf of $K$, the local inequalities
$a_{qL}-a_{qR}\ne1$ at its primitive cherries, and the integer $d\ge1$.
If $X$ is the resulting normal code, the source code is exactly

$$
F(X,\tau_dX),\qquad
r_{L p}=a_p,\quad r_{R p}=a_p+d.
\tag{SFP.20}
$$

Every original in (SFP.19) has these coordinates with $X=B(u)$.

Proof. Write an original with the first row as $t=\langle u,v\rangle$,
where $u\ne v$. Its second row is a pair with children $\rho^d u$ and
$\rho^d v$. The positive link says $v=\rho^d u$. If $d=0$, this
contradicts the first partition. If $d>0$, uniform translation of the
nonempty rank set in $B(u)$ excludes $u=\rho^d u$ and
$u=\rho^{2d}u$. For example their minimum ranks differ by $d$ and $2d$.
Injectivity of $\rho^d$ then gives the second row's distinct classes,
and the displayed negative link is satisfied. This proves both
inclusions of (SFP.19) for arbitrary $u$.

Every finite $u$ has exactly one normal $B(u)$, with precisely the local
rank constraints stated. If $X$ is nonprimitive, neither child in
$F(X,\tau_dX)$ is primitive. If $X=[a]$, its child ranks are $a,a+d$,
whose difference is $-d$, never $1$. The outer pair is consequently
normal in both cases. Equation (SFP.4) proves (SFP.20), and reading
its left subtree and the supplied lag proves reverse extraction.
No constant field or bounded shape is imposed on $X$. $\square$

**Theorem 6.3 (exact boundary memory and the conditions for recovery).**
For the family (SFP.19), the mathematical memory consisting of the actual
right-subtree value $v$ and its lag $d$ is equivalent to the full
original history. Its exact domain and decoder are

$$
\begin{aligned}
\mathcal M&=\{(v,d):v\in\mathcal T,\ d\ge1,
                          \min\operatorname{rank}(B(v))\ge d\},\\
u&=E(\tau_{-d}B(v)),\qquad
\operatorname{Recover}(v,d)
       =(\langle u,v\rangle,(0,d)).
\end{aligned}
\tag{SFP.21}
$$

The subtraction denotes the supplied code-image inverse, not a physical
backward update. The forward memory map takes $(t,(0,d))$ to $(t|_R,d)$.
The two maps are mutually inverse on the displayed domains. Consequently
this memory computes every original complete finite-cut row of that
source and every subsequent finite iterate and its complete rows.

Neither these two retained rows alone, nor $v$ alone, nor $u$ alone,
nor residual shape and lag alone, determine the full original in this
family. The same value memory is not a certificate of physical provenance.

Proof. In (SFP.19), $v=\rho^d u$, so ABC gives the rank lower bound and
its unique normal preimage. This proves both inverse identities in
(SFP.21). Conversely the lower bound makes subtraction natural and
normal, and ABC gives $\rho^d u=v$, hence (SFP.19). Once $t$ is
reconstructed, finite recursion computes any requested iterate and its
entire finite-cut exterior and partition; this is a mathematical
calculation on the supplied value.

All $u$ and all positive $d$ give the same two rows and links, so the
rows alone do not select a source. For $v=T_2$, both $(u,d)=(T_1,1)$
and $(T_0,2)$ are legal. They give different originals
$\langle\beta,T_2\rangle$ and $\langle\alpha,T_2\rangle$.
The original target cut $Q=\{LL,R\}$ has respective exteriors
$\langle\beta,\square_R\rangle$ and
$\langle\alpha,\square_R\rangle$: its $LL$ request is blocked at $L$.
Thus forgetting the lag loses even this concrete original row, while
retaining $v,d$ recovers it. Fixing $u=\alpha$ and taking $d=1,2$
likewise gives different sources, so $u$ alone is insufficient.
Finally $F([0],[0])$ and $F([0],[2])$ give different normal residuals
of the same shape at the same $d$, hence different originals by (SFP.20).

If $d=0$, the distinct-class rows fail. If the rank lower bound fails,
there is no native preimage for (SFP.21). If the retained subtree is
not the actual right value of the same continuing source, the inverse
identities provide no assertion about that physical source. These are
exact failed hypotheses of the recovery statement. $\square$

**Proposition 6.4 (an unbounded signed mismatch within linked rows).**
Let $h\ge1$ and let $K_h$ be the perfect full shape of height $h$.
Let $U_h$ label all its leaves by zero, and let $V_h$ have the same labels
except for rank $2$ at $R^h$. Put $u_h=E(U_h)$ and $v_h=E(V_h)$.
For every $d\ge1$, set

$$
t_{h,d}=\langle\langle u_h,\rho^d u_h\rangle,
                    \langle v_h,\rho^d v_h\rangle\rangle.
\tag{SFP.22}
$$

At epochs $0,d$ the cut $\{LL,LR,RL,RR\}$ has four distinct classes
and the same full pair-of-pairs exterior. The two positive links
$(0,LR)=(1,LL)$ and $(0,RR)=(1,RL)$ hold. The negative between the
values at $(0,LL)$ and $(0,RL)$ has identical normal shape on its two
sides and exactly one possible unequal leaf, at depth $h$.

Proof. All primitive-cherry differences in $U_h,V_h$ lie in
$\{-2,0,2\}$, so both codes are normal. Their ranks differ exactly at
$R^h$. Translating preserves their normality and their nonconstant
versus constant field distinction. At any fixed $d>0$, the four code
fields $U_h,\tau_dU_h,V_h,\tau_dV_h$ are pairwise different:
the first two are distinct constants; the last two are distinct
nonconstant fields; and a constant cannot equal a nonconstant field.
Applying $\tau_d$ gives the same conclusion at the second epoch.
All these codes are $F$-rooted, so assembling (SFP.22) introduces no
collapsing primitive cherry. Pair preservation proves the links.
The last assertion follows from the unique differing label and
normal-code injectivity. Thus any implementation that merges rank
fields from shape equality, or bounds negative witnesses at a fixed
code depth independent of residual shapes, fails this native family.
This is a falsifier for those shortcuts, not an impossibility result
for the representation in Section 2. $\square$

## 7. Mathematical operations, costs and the remaining bridge

**Definition 7.1 (the resource boundary).** For a supplied shape tuple
let $N=\sum_v|H_v|$, where nodes are counted with their occurrences,
and let $V,E,D$ be the rank-vertex, equality-edge and forbidden-difference
counts of Section 2. These quantities are finite but not bounded by
the finite record description alone. Coordinate admission consists of
finite traversals of those supplied shapes and certificates, forest
construction, affine arithmetic and the checks (SFP.10). Evaluating an
already specified coordinate requires no existential native solver.
The size and bit complexity of all parameters remain actual costs.

Native expansion has a separate output cost. If the decoded source code
has leaf ranks $r_p$, its native leaf count is
$\sum_p F_{r_p+1}$, with $F_1=F_2=1$, and its node count is

$$
2\sum_p F_{r_p+1}-1.
\tag{SFP.23}
$$

Indeed $T_0,T_1$ each have one leaf and the atomic recurrence adds leaf
counts; native pairing adds the leaf counts of its children. Every full
finite tree has twice its leaf count minus one nodes. Thus even a
one-leaf code with a binary-written large rank can have very large
expanded output. A finite scheme does not bound residual storage,
certificate depth, arithmetic bit lengths or decoding cost.

**Definition 7.2 (acquired versus mathematical memory).** The variables
$\mathbf K,\mathbf b,\boldsymbol\eta$, the original $t$, and the value
$v$ in Theorem 6.3 are supplied mathematical data for their respective
algorithms. Extraction from a supplied $(t,\mathbf n)$ does not assert
that a live observer holds those data. Actual source information still
comes from materialized original-root $\mathsf{Read}(p)$ operations on
one continuing source, with forward $\mathsf{ApplyRho}$ and any declared
halting contract. The raw counts of reads, updates and the sum of actual
address lengths are distinct from construction, expansion, retained
memory, authentication and physical time.

A physical implementation of (SFP.21) must justify acquisition of the
whole needed value or an equally sufficient record, the authentic lag,
the correspondence of every materialized address, and the identity of
the continuing source. With independent writers it must also justify
safety and liveness of the observation protocol. None of these follows
from equality of finite tree values. Two separate physical objects can
carry the same value and satisfy every equation in this volume.

**Problem 7.3 (remaining broad recovery obligation).** For an actual
retained finite record, characterize and acquire a sufficient boundary
state for a specified future recovery task while preserving the actual
read addresses, continuing-source condition, independent-writer safety
and liveness, and all cost coordinates. Theorem 4.1 represents all
compatible mathematical alternatives; it does not choose an adaptive
producer, prove a physical clock, or decide unrestricted stopping.

A sharper representation-theoretic problem is to decide which target
maps are constant on equivalence classes obtained by forgetting selected
coordinates of (SFP.12), uniformly over arbitrary residual shapes.
For a particular map and particular forgotten coordinates this requires
its own proof or a precisely applicable supplier. General all-source
inclusion/equality and arbitrary tree-quantifier alternation are not
established here. Existence, uniqueness, representation, universal
invariance and actual acquisition are separate obligations.

## 8. Source interfaces and literature scope

**Convention 8.1 (exact repository interfaces).** The mathematical
input suppliers in this volume are NCE, ABC, NSF, NIC and PDC with the
ranges specified in Convention 1.3. Their underlying relevant source
interfaces have the following narrower meanings.

| Source interface | Exact scope retained here |
| --- | --- |
| [NativeCutFibers][CUT] and [its Scribe][CUTS] | `LegalValues` is injective on all appearing classes; `rowFiberEquiv` concerns an actual canonical row. Its inverse `recover` and private `recover_fill`/`fill_injective` establish the same-value filling correspondence. It does not by itself validate arbitrary proposed records. |
| [ActualCutPartitionDecoder][ROW] and [its Scribe][ROWS] | `literalRecord`, `actualPartition` and `canonicalRow_record_iff` relate the literal exterior and entire addressed partition to canonical rows. The private `eraseClasses_literal` participates in that bridge. Common-suffix recutting is a separate existing result. |
| [NativeDepthPatterns][DEPTH] and [its Scribe][DEPTHS] | `depthEquiv` retains arbitrary actual frontier subtrees, via private `fill_decompose` and `decompose_fill`. `original_present_transport` requires original presence; `original_prefix_locality` concerns replies. This is not an unknown-epoch signed rank-field representation. |
| [NativeBirthVectorDecoder][BIRTH] and [its Scribe][BIRTHS] | `birthVector_decompose` and `decodeBirth_patternVector` recover a finite `Pattern`, not the unrestricted frontier values. `birthAt` is a recursive code; its interpretation as least physical presence time is a separate bridge. Decoder acceptance on an arbitrary vector is not an image-membership certificate. |
| [NativeGroundSolutionSpace][GROUND] and [its Scribe][GROUNDS] | `Ext_sol`, `Ext_restriction`, `restriction_Ext`, `solutionEquiv` and `constrainedEquiv` retain every native free-constructor solution; the last keeps its arbitrary predicate pulled back along `Ext`. The grammar contains no interpreted unknown power of $\rho$. The present output does not use an arbitrary predicate as a solved domain. |
| [SourceTransportCentralizer][CENTRAL] and [its Scribe][CENTRALS] | `source_transport_centralizer` supplies native iterate injectivity and an inverse on the actual image, with the two Boolean generators and ordered pairing. An image inverse is not a reset operation on a live register. |

The affine construction uses ABC's normal-code correspondence. The
listed interfaces do not themselves establish Theorem 4.1.

**Convention 8.2 (primary literature and its languages).** The following
are `literature-attested` methodological suppliers or comparisons; the
native assembly in Lemma 3.3, Theorem 4.1 and their applications is
`repo-derived`, with no worldwide originality claim.

| Primary source | Mathematical scope and use |
| --- | --- |
| Baader–Snyder, *Unification Theory*, Chapter 8, §2.2.4, pp. 450–452, Lemma 2.2, Corollary 2.3, Lemma 2.4, Theorems 2.5–2.6 [BS] | Finite syntactic equations over free constructors have terminating solved-form transformation, an idempotent unifier, and factorization of every unifier. Used solely for the $c,f$ shape equations after collapse splitting. The chapter's §3 distinguishes complete sets modulo a specified equational theory; it does not identify this native interpreted theory with the free one. |
| Comon–Lescanne, *Equational Problems and Disunification*, §§4.2, 5.2–5.3, Theorems 2–4 [CL] | Equations/disequations and first-order equational problems over specified term algebras, with solved forms and terminating transformations. The finite Herbrand term domain and rational-tree cases are distinguished. These are precedents for complete solution descriptions, not a transfer theorem for unknown powers of the native substitution or its normal subdomain. |
| Kuncak–Rinard, *On the Theory of Structural Subtyping*, arXiv:cs/0408015v1, Figure 9, Theorem 90 and Corollary 91, §6.6 [KR] | The linked version's term-power quantifier-elimination and decidability results concern the stated four-sort language over a decidable base structure. Section 6.6 treats a selected-leaf/element operation as a different extension and explains why stronger decidability is not automatic. The present finite supplied-shape traversals do not assert definability or quantifier elimination in that ambient language. |
| Marshall–Meadows–Narendran, *On Unification Modulo One-Sided Distributivity: Algorithms, Variants and Asymmetry*, arXiv:1503.06687v2, §§3, 5 [MMN] | Equational unification under one-sided distributivity; the single-homomorphism case uses a specified two-sort discipline. Its homomorphism paths suggest offset graphs, but its equational signature, substitutions and solution order are different. It supplies no normality, negative-witness or source-preserving theorem for (SFP.1). |
| Cerna, *Schematic Unification*, arXiv:2306.09152v7, Definitions 5–7, 17, Theorems 6–8 [CERNA] | Indexed substitution schemas ask for unifiability of every instance. Uniformity and the stated infinity-stability condition govern the completeness guarantee. This is not the quantifier pattern of all ground common-source solutions at freely supplied chronological tuples. No native completeness or undecidability claim is borrowed. |

[TPO][TPO] separately identifies the normal-domain obstacle in the
specified ambient term-power language. This volume handles normality
by explicit finite traversal of each supplied shape, which is an allowed
operation of Definition 2.1. It does not assert that this traversal or
its selected mismatch leaves are definable in TPO's ambient language.
Nor does the absence of a matching literature theorem prove that no
other complete representation or decision procedure exists.

[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CROSS_EPOCH_RELATIONS.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[PDC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_POSITIVE_DOMAIN_CORRESPONDENCE.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[CUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[CUTS]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.scribe.cs
[ROW]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[ROWS]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.scribe.cs
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[DEPTHS]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.scribe.cs
[BIRTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.lean
[BIRTHS]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.scribe.cs
[GROUND]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.lean
[GROUNDS]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.scribe.cs
[CENTRAL]: ../../../D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[CENTRALS]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.scribe.cs
[BS]: https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[KR]: https://arxiv.org/pdf/cs/0408015v1
[MMN]: https://arxiv.org/pdf/1503.06687v2
[CERNA]: https://arxiv.org/pdf/2306.09152v7

## 追加锚（本行以下为增补区）
