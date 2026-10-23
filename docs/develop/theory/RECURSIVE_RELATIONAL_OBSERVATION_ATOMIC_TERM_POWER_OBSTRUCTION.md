# Finite term-power expressions and the atomic normal-domain obstruction

## 1. The ambient structure and the native domain

**Definition 1.1 (the two tree domains).** Use the ambient term algebra
and native domain of [ABC, Definition 2.1][ABC]:

$$
\begin{aligned}
\mathcal K&::=[j]\ (j\in\mathbb N)\mid F(\mathcal K,\mathcal K),\\
[j]&\in\mathcal N,\\
F(X,Y)\in\mathcal N
&\ \Longleftrightarrow\ X,Y\in\mathcal N\ \land\
 \neg\exists j\in\mathbb N\ (X=[j+1]\land Y=[j]).
\end{aligned}
\tag{TPO.1}
$$

Thus normality forbids one oriented primitive-sibling relation at every
internal occurrence. Ambient pairing is the free constructor $F$.
Native pairing on normal codes is ABC's smart constructor $J$, which
collapses $F([j+1],[j])$ to $[j+2]$.

The original sources and forward action remain

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad\rho\beta=\langle\beta,\alpha\rangle,
\quad\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
\tag{TPO.2}
$$

Write $T_j=\rho^j\alpha$. The supplied maps are
$E([j])=T_j$, $E(F(X,Y))=\langle E(X),E(Y)\rangle$ and
$B:\mathcal T\to\mathcal N$. By [ABC, Theorems 2.2–2.3][ABC],
$B$ and $E|_{\mathcal N}$ are inverse bijections, and
$B(\rho^m u)=\tau_mB(u)$, where $\tau_m$ adds $m$ to every primitive
rank. These are supplied structural correspondences on all finite
sources, with no bound on their size or depth.

**Definition 1.2 (the exact four-sort language).** Let $\mathfrak A$
be exactly [ABC, Definition 7.1][ABC], namely the covariant
$\{F\}$-term-power of the relational presentation of
$(\mathbb N,0,1,+,\le)$. Its language and partial semantics are
[Kuncak–Rinard, *On the Theory of Structural Subtyping*,
arXiv:cs/0408015v1, §§6.1–6.4, Figures 9–11][KR]. The four sorts are:

| Sort | Values |
| --- | --- |
| $\mathsf{term}$ | $\mathcal K$ |
| $\mathsf{shape}$ | finite ordered $F^S$-trees over the one-leaf shape $c$ |
| $\mathsf{leafset}$ | $(s,A)$ with $A\subseteq\operatorname{Leaves}(s)$ |
| $\mathsf{bool}$ | the truth values $\mathsf{true},\mathsf{false},\mathsf{undef}$ of the partial logic |

Let $\operatorname{sh}(X)$ forget primitive ranks and let
$\operatorname{lssh}(s,A)=s$. Leaves are finite $L/R$ words. The term
algebra has $F$, its two partial selectors, its constructor test and its
primitive test. The shape algebra has $c,F^S$, constructor tests and
partial selectors. The leafset algebra has $F^L$, constructor and
primitive tests, partial selectors and $\operatorname{lssh}$, with

$$
F^L((s,A),(t,C))
 =(F^S(s,t),\ LA\cup RC).
\tag{TPO.3}
$$

Its left selector returns $(s,A)$ and its right selector returns $(t,C)$.
This is the constructor-inverse semantics of KR Figure 11.

For each shape $s$ there are full and empty leafsets, intersection,
union and complement relative to $\operatorname{Leaves}(s)$. For every
first-order base formula $\theta$ with $r$ free rank variables, including
arbitrary first-order quantifiers within the base formula, the inner
formula instance is

$$
[\theta]^I_s(X_1,\ldots,X_r)
 =\left(s,\{w\in\operatorname{Leaves}(s):
       \mathbb N\models\theta(X_1[w],\ldots,X_r[w])\}\right).
\tag{TPO.4}
$$

It is defined when every $X_i$ has shape $s$. Addition and constants in
$\theta$ use their relational graphs if required. This does not introduce
an outer scalar sort or a map selecting the rank at a variable leaf.
The inner existential and universal binders are the pointwise union and
intersection binders of KR Figure 10; an inner formula instance has
exactly the semantics (TPO.4).

The outer operations are equality on terms, shapes and tagged leafsets,
constructor and primitive tests, and cardinality predicates
$|A|_s=k$ and $|A|_s\ge k$ for each fixed numeral $k\ge0$. Outer logical
connectives have KR's partial truth tables. Outer quantification ranges
over terms, shapes and leafsets. There is no quantifier over leaf
addresses among these operations. The sort $\mathsf{bool}$ is the
truth-value sort, not an additional sort of source indices.

Selectors are defined exactly at the corresponding constructor. An
inner relation or Boolean leafset operation requires its term shapes or
leafset tags to equal the supplied shape. A cardinality predicate requires
the correct tag. Equality of two defined leafsets with different tags is
false, not an equality of untagged sets. The other nonlogical operations
are strict. These, together with defined arguments, are all the
partial-operation conditions used below. On guarded formulas the truth
value is ordinary Boolean; equality of partial truth values will also
be preserved whenever an intermediate expression is undefined.

Primitive numerals $[j]$ may be denoted as finite definitional
abbreviations: the primitive test and the lifted predicate $x=j$ at $c$
define their unique values. A fixed-numeral translation or another
operation from [ABC, Theorem 7.2][ABC] likewise means its given finite
graph formula, not an extra primitive operation on unknown subterms.

**Definition 1.3 (finite parameters and the logical supplier).** A
parameter tuple $\bar a$ consists of finitely many fixed elements of
the term, shape and leafset sorts, and, if present as truth constants,
fixed Boolean values. All its trees and leafsets are finite. Its values
are fixed before the varying input $X$ is chosen. In particular the tuple
cannot contain a family of shapes, a leaf-selector oracle, or parameters
chosen as a function of $X$.

The logical supplier used here is precisely [KR, Lemma 47, Proposition 55, Theorem 56(a)
and Corollary 57][KR]. Lemma 47 replaces a well-defined Figure 9 formula
by a well-defined simple formula: lifted relations and inner quantifiers
occur within instances of base inner formulas. Theorem 56(a) produces
an equivalent finite formula in selector language without the outer
term, shape and leafset quantifiers. Its remaining inner quantifiers
are permitted within (TPO.4); they are not discarded. KR's Proposition 55, using Corollary 51,
gives this selector form in the simple language. Corollary 57 supplies decision of sentences when
the base theory is decidable. No subterm quantifier, recursive predicate
or arbitrary-element selection is added by these statements. KR §6.6
treats element selection separately.

These cited results are suppliers. The finite-expression invariance
proved below concerns their selector output and the particular native
domain (TPO.1). It uses no decision result about arbitrary inductively
specified subsets of $\mathcal K$.

## 2. Perfect witnesses and finite shape diagrams

**Definition 2.1 (opposite bottom orientations).** Put
$S_0=c$ and $S_{h+1}=F^S(S_h,S_h)$. For $k\in\mathbb N$ define

$$
\begin{aligned}
U^+_{1,k}&=F([k],[k+1]),&
U^-_{1,k}&=F([k+1],[k]),\\
U^\pm_{h+1,k}&=F(U^\pm_{h,k},U^\pm_{h,k})&& (h\ge1).
\end{aligned}
\tag{TPO.5}
$$

Both have shape $S_h$. At a leaf of $U^+_{h,k}$ the rank is $k$ when
the last edge is $L$, and $k+1$ when it is $R$. The two ranks are
interchanged in $U^-_{h,k}$. A selector word $p$ of length $d<h$
returns exactly $U^\pm_{h-d,k}$, irrespective of the letters in $p$.
Let $\overline L=R$ and $\overline R=L$.

**Lemma 2.2 (normality separates every witness pair).** For every
$h\ge1$ and $k\ge0$,

$$
U^+_{h,k}\in\mathcal N,
\qquad U^-_{h,k}\notin\mathcal N.
\tag{TPO.6}
$$

Both heights and primitive ranks in this family are unbounded. In
particular $U^+_{h,h}$ is a normal code for the actual native source
$E(U^+_{h,h})$ for every $h\ge1$.

Proof. The only nodes with two primitive children are the bottom
cherries. Their left and right ranks in $U^+_{h,k}$ are $k,k+1$, so the
forbidden equation would be $k=(k+1)+1$, which is false in $\mathbb N$.
Every bottom cherry of $U^-_{h,k}$ is instead exactly the forbidden
$F([k+1],[k])$. All higher children are nonprimitive and introduce no
additional primitive-sibling condition. This proves (TPO.6).
Choosing $k=h\to\infty$ proves the last claims, using ABC's source
bijection. The negative witness is an ambient code, as required when
testing a formula intended to select $\mathcal N$ inside $\mathcal K$;
it is not claimed to be a second normal representative. $\square$

**Definition 2.3 (finite selector diagrams).** A finite selector diagram
is a finite family of outer-quantifier-free simple expressions, closed
under subexpressions and including the shape of every term and leafset
expression. It may contain finite constructor contexts with repeated
occurrences of $X$, arbitrary finite compositions of selectors in all
three tree sorts, and all the operations of Definition 1.2. Its only
unfixed free variable is one term variable $X$; its other free values
are a fixed tuple $\bar a$ as in Definition 1.3.

An inner instance is treated as one leafset-producing node with its
finite tuple of term arguments and shape argument. Its base formula
may have any finite number and alternation of rank quantifiers. The
syntax inside that base formula does not select positions of its outer
term arguments. Definedness conditions and any finite Boolean
combinations of them are included in the diagram.

A shape skeleton is a finite ordered constructor context whose leaves
are either $c$ or symbols $Z_p$, where $p$ is a finite selector word.
At the varying shape $S_h$, $Z_p$ denotes its selected shape
$S_{h-|p|}$ when $|p|\le h$. This notation is used to analyze a finite
expression, not as an additional language operation.

**Lemma 2.4 (effective finite separation of ground and variable leaves).**
For a finite selector diagram $\mathcal D$ and fixed $\bar a$, one can
choose an integer $b\ge2$ such that for every $h>2b+2$ and $k\ge0$ the
following statements hold under $X=U^+_{h,k}$ and $X=U^-_{h,k}$.

1. Every non-Boolean subexpression is defined in both evaluations or
   in neither. Defined term and leafset expressions have the same shape
   in both. Every domain guard for a primitive operation agrees.
2. Every such shape, including every explicit shape expression, has a
   skeleton in which the context height and all $|p|$ are at most $b$.
   Leaves outside the $Z_p$ blocks have depth at most $b$; every leaf
   inside a $Z_p$ block has depth at least $h-b>b+2$.
3. Every leaf of depth greater than $b$ is in one of these perfect
   blocks, has a sibling leaf, and that sibling belongs to the same
   block. In every term expression the labels outside the blocks are
   independent of the choice of sign. Inside a block the labels have
   the bottom orientation of that sign.

The same $b$ works for all $k$. It is allowed to depend on the finite
shapes of the parameters, but not on their changing with $h$.

Proof. Expand the shapes of the fixed parameters into their finite
$c,F^S$ trees. For term expressions use the homomorphism rules

$$
\operatorname{sh}(F(t,u))=F^S(\operatorname{sh}t,\operatorname{sh}u),
\qquad
\operatorname{sh}(F_i(t))=F_i^S(\operatorname{sh}t)
\tag{TPO.7}
$$

on the selector's domain. For leafset expressions use the corresponding
rules for $F^L$ and its selectors. The shape of a defined inner
instance, full or empty leafset, or indexed Boolean leafset operation
is its displayed shape index. Thus erasing a shape or a tag recursively
reduces to a finite shape expression built from $c$, constructors,
selectors and $Z_\varepsilon=\operatorname{sh}(X)$.

Cancel a selector applied to a displayed constructor. A selector
reaching $Z_p$ produces $Z_{pL}$ or $Z_{pR}$; a selector reaching $c$
is undefined. Every cancellation consumes an occurrence from the
finite expression. Expanding a fixed parameter consumes its fixed
finite tree. This yields finitely many skeletons for all shape
expressions, implicit tags and operation arguments. There are also
finitely many domain requirements: a selected root must be a constructor,
and specified shapes or tags must agree. Choose $b\ge2$ larger than
or equal to all resulting context heights and selector-word lengths.
Taking a larger integer accommodates every intermediate argument and
result, not just the final expressions.

For $h>2b+2$, every $Z_p$ is a perfect tree of height at least
$h-b>b+2$. Hence it is nonprimitive wherever one of the finitely many
selectors reaches it. The skeleton evaluation is independent of $k$
and of the sign. Equality of two shape values is therefore identical
in the two evaluations, whether or not those values have the same
skeleton description. Constructor tests are also identical. Induction
through the operation domains now proves simultaneous definedness:
all selector domains and all tag-matching domains agree, base relations
are total on their rank tuples, and a simple inner instance has precisely
the same-shape domain in (TPO.4). Strict undefined arguments propagate
through non-Boolean expressions in both evaluations. The domains of primitive Boolean tests agree too;
their truth values and the possibly nonstrict outer Boolean connectives
are treated in Theorem 3.1. No rank-sensitive Boolean test controls the
domain of a primitive nonlogical operation in this signature.

A leaf contributed by the finite context has depth at most $b$. A leaf
in a block $Z_p$ attached at context address $v$ has depth
$|v|+h-|p|\ge h-b$. Its last edge is strictly inside that block, and
its sibling is another leaf of the block. The term-algebra version of
the cancellation argument leaves only fixed ground pieces and selected
copies of $X$. The latter are $U^\pm_{h-|p|,k}$, so their labels have
the stated orientation; fixed ground pieces retain their labels.
Leafset membership is not asserted to be independent of sign here:
only its shape and definedness have been established. $\square$

**Definition 2.5 (one permutation for each evaluated shape).** For a
shape $s$ occurring in Lemma 2.4 define $\sigma_s$ on its leaves by

$$
\sigma_s(w)=
\begin{cases}
w,&|w|\le b,\\
v\overline e,&w=ve,\ |w|>b.
\end{cases}
\tag{TPO.8}
$$

The second case is defined because its leaves come in sibling pairs.
It is an involution. Its definition depends on the actual shape and
$b$, not on a particular context presentation or expression producing
that shape. In particular equal shapes always receive the same
permutation.

**Lemma 2.6 (alignment across finite contexts and selectors).** At every
constructor or selector occurrence of the diagram, the permutations
commute with its maps on leaves. In particular, when
$s=F^S(s_L,s_R)$ at a constructor occurrence, or for the selected
child at a selector occurrence,

$$
\sigma_s(ew)=e\sigma_{s_e}(w)
\quad(w\in\operatorname{Leaves}(s_e)),
\tag{TPO.9}
$$

where $e$ is either child of a constructor or the indicated selector
child. The assertion includes shapes of term constructors, shape
constructors, leafset constructors, and their respective selectors.

Proof. Lemma 2.4 applies simultaneously to the child and parent shapes
in each displayed occurrence. A fixed-context leaf remains a
fixed-context leaf when one outer prefix is inserted or removed, so
its depth in both expressions is at most $b$ and both permutations
fix it. A variable-block leaf remains within a corresponding perfect block
with one outer prefix inserted or removed. If the selector acts on a
block itself, its selected half is still perfect and has height greater
than $b+2$ by the bound for the result expression. Its depth in both expressions
exceeds $b+2$, and its final edge is unchanged by that insertion or
removal. Both permutations flip that same final edge. This proves
(TPO.9). A selector is the inverse restriction to the specified cone,
so obeys the same identity in the reverse direction.

This proof also covers cancellations such as selecting through a
constructor context that contains several copies of selected $X$.
If distinct context presentations have equal evaluated shapes, (TPO.8)
assigns them one and the same permutation: a coordinate of depth at most
$b$ is fixed in every presentation, and a deeper coordinate is flipped
in every presentation. Thus an aligned comparison cannot use different
permutations for its different arguments. No unique context presentation
or global tree-algebra automorphism is required. $\square$

## 3. Invariance of the complete finite expression language

**Theorem 3.1 (finite-expression and selector invariance).** Let
$\mathcal D,\bar a,b$ be as in Lemma 2.4. For all $h>2b+2$ and $k\ge0$,
write $e^+$ and $e^-$ for the evaluations with $X=U^+_{h,k}$ and
$X=U^-_{h,k}$. Every expression has the same definedness in both.
For defined expressions the following hold:

$$
\begin{array}{c|l}
\text{sort of }e&\text{correspondence}\\\hline
\mathsf{shape}&e^+=e^-\\
\mathsf{term},\ \operatorname{sh}(e^\pm)=s
 &e^+[w]=e^-[\sigma_s(w)]\quad(w\in\operatorname{Leaves}(s))\\
\mathsf{leafset},\ e^\pm=(s,A^\pm)
 &A^-=\sigma_s[A^+]\\
\mathsf{bool}&e^+=e^-.
\end{array}
\tag{TPO.10}
$$

In particular every Boolean expression in the diagram has the same
truth value. The result covers full leafsets and their selectors,
cardinality tests, arbitrary finite constructor contexts, repeated
arguments and all remaining inner arithmetic quantifiers.

Proof. Non-Boolean definedness, primitive-operation domains and the
shape case are Lemma 2.4. We prove the other cases, including equality
of outer partial truth values, simultaneously through the finite
expression diagram.

For $X$, flipping the last edge exchanges exactly the two bottom rank
positions in (TPO.5); this gives the term assertion at every leaf.
Every fixed parameter has only shallow leaves in this diagram, so
$\sigma$ fixes its positions and the assertion is immediate for both
term and leafset parameters. A primitive numeral, if retained as a
fixed finite value, is included in this case.

Term constructors preserve the assertion by (TPO.9), applied to their
two children. Term selectors preserve it by the inverse cone identity.
The tests for a term constructor or a primitive depend only on the
shape. Equality of two defined terms with different shapes is false
in both evaluations. If their shapes agree, they use the same
$\sigma_s$; equality is equivalent to equality of their primitive
values at every aligned leaf. The common permutation and the inductive
term assertion preserve that condition in both directions.

Consider an inner instance $[\theta]^I_s(t_1,\ldots,t_r)$. If a shape
guard fails, it fails on both sides. Otherwise, for every leaf $w$,

$$
(t_1^+[w],\ldots,t_r^+[w])
 =(t_1^-[\sigma_s(w)],\ldots,t_r^-[\sigma_s(w)]).
\tag{TPO.11}
$$

The base structure is unchanged. Hence every first-order base formula
$\theta$ has the same truth value on these identical tuples. To make
the quantifier case explicit, if
$\theta(\bar z)=\exists n\,\eta(\bar z,n)$, each witness
$n\in\mathbb N$ on one side is that very same witness on the other;
the inductive assertion for $\eta$ gives both implications. For
$\forall n$ the comparison uses the same complete set $\mathbb N$.
Boolean connectives and additional quantifier alternations follow by
induction. This is equality of tuples, not an automorphism or an
approximation of arithmetic.

Equivalently, at the inner term-quantifier level, terms of shape $s$
are all assignments of natural values to its finitely many leaves.
For an existential test at one leaf every natural witness can be
completed at the other leaves, for example with zeros. The map
$Z\mapsto Z'$ specified by $Z'[\sigma_s(w)]=Z[w]$ is a bijection of
these assignments, so the pointwise unions and intersections agree
under $\sigma_s$. This proves the inner-binder case directly from KR
Figure 10 as well as from (TPO.4). No inner witness is required to be
native normal; its quantifier is the ambient same-shape quantifier.
Thus (TPO.11) proves the leafset assertion for each inner instance.

Full and empty leafsets are preserved by every permutation. A bijection
commutes with union, intersection and relative complement, so all the
indexed Boolean leafset operations preserve the assertion when their
tags match. Leafset constructors preserve it by the disjoint-cone
formula (TPO.3) and (TPO.9). Leafset selectors preserve it by restriction
to the selected cone and removal of its first edge. This handles any
finite alternation of these operations and inner instances.
Leafset shape, constructor tests and primitive tests depend only on
the preserved tag. Equality of two leafsets with unequal tags is false
on both sides; with equal tags, the same bijection preserves equality
and inequality of their subsets. Cardinalities are identical under a
bijection, so $=k$ and $\ge k$ have equal truth values for every numeral
$k$, including zero. Their tag guards have already been preserved.

Shape constructors, selectors and tests are covered by the shape
assertion, including tests against $c$. Undefined arguments and failed
guards produce the same partial values. Finally each outer Boolean
connective has identical input truth values, so its prescribed truth
table has identical output, including all undefined cases. On a guarded
formula this is equality of ordinary truth values. These cases exhaust
the operations in Definitions 1.2–1.3 after simplification and outer
quantifier elimination. $\square$

**Proposition 3.2 (the height bound is necessary; leafwise arithmetic
is retained).** The formula that tests whether the left child of $X$
has the primitive rank of the right child plus one separates
$U^+_{1,k}$ from $U^-_{1,k}$ for every $k$. Conversely the inner formula
$[z=k]^I_{\operatorname{sh}(X)}(X)$, for any fixed numeral $k$,
inspects primitive ranks
at every leaf of $U^\pm_{h,k}$, however large $h$ is, and its cardinality
is $2^{h-1}$ for both orientations.

Proof. At height one the two children are primitive, so the lifted
successor predicate at shape $c$ is false for $(k,k+1)$ and true for
$(k+1,k)$. At height $h$ each orientation has exactly one rank-$k$
leaf in each of its $2^{h-1}$ bottom cherries. The two satisfying
leafsets are different but are carried to one another by (TPO.8).
Thus the invariance theorem is neither a statement about all heights
nor a claim that inner formulas inspect only a bounded prefix. $\square$

## 4. Eventual indistinguishability and nondefinability

**Theorem 4.1 (formula-dependent eventual indistinguishability).** For
every well-defined finite unary formula $\varphi(X;\bar a)$ in exactly
Definition 1.2, with fixed finite parameters as in Definition 1.3,
there exists an effectively obtainable $H\ge1$ such that

$$
\forall h\ge H\ \forall k\ge0,\qquad
\mathfrak A\models\varphi(U^+_{h,k};\bar a)
\ \Longleftrightarrow\
\mathfrak A\models\varphi(U^-_{h,k};\bar a).
\tag{TPO.12}
$$

Here effectivity uses the cited KR formula transformations and the
supplied finite parameter values. The same statement holds for any
finite collection of such formulas by taking the maximum of their
bounds.

Proof. Apply the finite simplification and outer quantifier-elimination
supplier of Definition 1.3. Retain all inner base formulas, including
their quantifiers. The result is an equivalent finite selector formula
$\psi(X;\bar a)$ with no additional free variables. Close its finite
expressions under the subexpressions and implicit shapes of Definition
2.3. Lemma 2.4 computes a suitable $b$. Set $H=2b+3$.
Theorem 3.1 gives equal truth values of $\psi$ on each displayed pair
for all $h\ge H,k\ge0$. Equivalence of the original and transformed
formulas gives (TPO.12).

Each transformation operates on finite syntax. Parameter shapes are
finite trees; the skeleton reductions terminate by consuming that
syntax. Thus construction of $H$ has a stopping argument, independent
of a search through witness heights. This does not eliminate the
remaining inner rank quantifiers by bounded sampling. $\square$

**Corollary 4.2 (no uniform native-domain formula).** There is no
well-defined finite formula $\mathsf{Normal}(X;\bar a)$ in exactly
Definition 1.2, with any fixed finite parameter tuple, such that

$$
\forall X\in\mathcal K,\qquad
\mathfrak A\models\mathsf{Normal}(X;\bar a)
\ \Longleftrightarrow\ X\in\mathcal N.
\tag{TPO.13}
$$

Consequently [ABC, Assumption 7.3][ABC], with its stated language and
all-shape native domain, cannot be supplied.

Proof. Apply Theorem 4.1 to a proposed formula and choose $h\ge H$,
$k=h$. Lemma 2.2 puts $U^+_{h,h}$ in $\mathcal N$ and excludes
$U^-_{h,h}$, whereas (TPO.12) gives the same truth value. This contradicts
(TPO.13). The witnesses have arbitrarily large heights and ranks;
no finite rank range or supplied shape is a premise. ABC Assumption
7.3 is the parameter-free special case. $\square$

**Corollary 4.3 (finite eliminable abbreviations do not define normality).**
The conclusion of Corollary 4.2 holds after adjoining finitely many
acyclic explicit formula abbreviations and explicitly definable
function symbols whose finite guarded graph expansions eliminate them
back to Definition 1.2. All parameters in those definitions must be a
fixed finite tuple independent of $X$.

Proof. Expand predicate abbreviations in dependency order, renaming
bound variables to avoid capture. Replace each defined function
occurrence by a fresh variable and its graph, with the domain condition
required by its partial semantics. For a partial graph $G(\bar t,y)$
the domain is $\exists y\,G(\bar t,y)$; functionality makes the value
unique when that domain holds. Guarded case expansion preserves the
false and undefined branches as well as the defined branch. By the
assumed finite elimination property this produces a finite formula in
the original language, possibly with outer quantifiers. Acyclicity
ensures expansion terminates. The union of all parameter tuples is
still fixed and finite. A definition of $\mathcal N$ in the expanded
notation would therefore contradict Corollary 4.2 after expansion and
Theorem 4.1's quantifier elimination.

In particular the fixed-numeral and fixed-address formulas of
[ABC, Theorem 7.2][ABC] are available as abbreviations with their actual
guards. An unbounded recursive scheme, a primitive native-normality
predicate or an arbitrary-address operation is not such a finite
eliminable abbreviation. $\square$

**Corollary 4.4 (the total canonicalization graph is not definable).**
Define the total mathematical map

$$
C:\mathcal K\to\mathcal N,\qquad C(X)=B(E(X)).
\tag{TPO.14}
$$

There is no well-defined finite formula $G(X,Y;\bar a)$ in the language
of Definition 1.2, even with fixed finite parameters, satisfying

$$
\forall X,Y\in\mathcal K,\qquad
\mathfrak A\models G(X,Y;\bar a)
\ \Longleftrightarrow\ Y=C(X).
\tag{TPO.15}
$$

The assertion also holds under the finite expansions of Corollary 4.3.

Proof. ABC's inverse identities give $C(X)=X$ for $X\in\mathcal N$.
Conversely $C(X)$ is always normal, so $C(X)=X$ implies
$X\in\mathcal N$. Substitution $Y=X$ in a formula satisfying (TPO.15)
would make $G(X,X;\bar a)$ a formula satisfying (TPO.13), contrary to
Corollary 4.2. This uses correctness of the graph on all ambient
arguments. A graph promised correct only for already-normal inputs,
where $C$ is the identity, has no such consequence. $\square$

## 5. The interpretation boundary and the retained recovery problem

**Definition 5.1 (the unchanged acquired source and consumer).** The
recovery problem is [ARH, Assumption 1.3 and Definition 9.1][ARH], with
[ABC, Assumption 1.2][ABC]'s same-source presentation. Its input consists
of an old full row $R_P(u)=R$, finite literal history $H_0$, finite signed
whole-subtree history $H_{\rm rel}$ and authentic entry epoch $N$ at
least every acquired epoch. Its entire nonempty source fiber is

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{TPO.16}
$$

A record $(a,s,b,t,\bowtie)$ requires that both physical endpoints exist
and that $(\rho^a u)|_s\ \bowtie\ (\rho^b u)|_t$, for
$\bowtie\in\{=,\ne\}$. Absence invalidates either sign. All old
repeated classes, cross-class and off-task disequalities, old guards
and further records remain jointly imposed on the same original source.
The complete accessible handoff includes every source-bearing cache,
address, count, length, control state, timing field, reference, permission
and archive. Relations were actually acquired before the cut; their
acquisition may be finite sourcewise without a uniform bound.

The output is the entire original row $R_Q(u)$: reached original holes,
concrete exterior and the full equality partition. Deterministic effective
source-total services act on the same original-root register, initially
$\rho^N u$, using physical reads at arbitrary finite literal words,
forward actual $\mathsf{ApplyRho}$ and absorbing halt. Their common
control may depend on acquired replies. There is no equality query,
reset, reroot, clone, source identity or uncharged source-dependent
input. A simulated event supplies no actual receipt.

For a service $A$, the three distinct resource objects are

$$
\begin{aligned}
c_A(u)&=(q_A(u),a_A(u),\ell_A(u)),
&\ell_A(u)&=\sum_{\text{actual read words }p}|p|,\\
b(A)&=(\sup_Dq_A,\sup_Da_A,\sup_D\ell_A),
&W_\lambda(A)&=\sup_{u\in D}\lambda\cdot c_A(u),
\quad\lambda\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{TPO.17}
$$

Here $q$ counts every raw call and $a$ actual post-entry updates. The
weighted sum is formed on one source before taking its supremum.
Computation, address generation, installation, storage, authentication,
retention and physical time remain separate quantities.

**Proposition 5.2 (the precise excluded logical inference).** The
normal-domain step proposed in [ABC, Assumption 7.3 and Propositions
7.5–7.6][ABC] cannot be implemented by a finite formula of its stated
ambient language, nor by the total canonicalization graph (TPO.15).
This exclusion concerns that interpretation step. It leaves the
all-source correspondences of ABC §§2–6 and the fixed-numeral,
fixed-address operation formulas of ABC Theorem 7.2 intact, as well as
ABC Proposition 7.4's normality formulas for a supplied finite shape.
It supplies
no undecidability theorem for (TPO.16), no physical impossibility theorem
and no general failure of bounded full-row recovery.

Proof. The excluded domain formula is exactly (TPO.13), and the proposed
graph is (TPO.15), so Corollaries 4.2 and 4.4 apply. ABC's structural
proofs use induction on supplied finite trees and the maps $B,E,J$;
they do not assume that $\mathcal N$ is a definable ambient subset.
ABC Theorem 7.2 explicitly asserts the meanings of its finite graphs
on normal arguments, not a formula restricting all quantifiers to
normal arguments. Those premises therefore do not invoke the excluded
formula. At a supplied finite shape, ABC Proposition 7.4 enumerates its
finitely many primitive cherries and tests their rank relations. The
formula-dependent choice of a larger witness height in Theorem 4.1
places no restriction on that fixed-shape result.

Its conditional Propositions 7.5–7.6 remain implications with
their stated additional premise; Corollary 4.2 prevents discharging that
premise in this language. They consequently provide no unconditional
algorithm by this particular route.

The nondefinability conclusion compares ambient representations with
different membership in $\mathcal N$. It gives no pair of sources in
a fixed acquired fiber with the same every permitted observation and
different required outputs. Nor does it reduce an undecidable problem
to acquired recovery. Indeed normality of a supplied finite code is
decided by traversing its finitely many cherries and testing the integer
successor relation. That ordinary decision coexists with Corollary 4.2.
An alternative exact interpretation in another language or with another
representation is not ruled out by a theorem about Definition 1.2.

Theorems 3.1–4.1 establish invariance under a permutation chosen for a
finite formula and parameter tuple. They do not establish a global
automorphism: the height-one separating formula of Proposition 3.2
already forbids that conclusion. Thus they also do not identify ordered
native sources, native actions or acquired histories. $\square$

**Definition 5.3 (supplied correspondences and scoped effective results).**
The following are the existing suppliers for (TPO.16)–(TPO.17). They
specify the mathematical premises that remain available after
Proposition 5.2; none is an additional consequence of term-power
decidability.

1. [ABC, Theorems 3.2, 4.2, 5.2 and 6.2, Corollary 6.3][ABC] give
   guarded original physical navigation, the complete original row,
   both inclusions of the entire acquired fiber and both paid adaptive
   controller directions under $u\leftrightarrow B(u)$. They preserve
   each actual source's $c_A(u)$ exactly, before either kind of supremum.
   The coded register is opaque; its ranks, shape and code are not new
   accessible data. These statements include zero epochs, absent
   addresses, repeated calls, early halt and all permitted adaptive
   serial competitors.
2. [ARH, §§2–3][ARH] give the exact guarded morphic cells and static/serial
   bounded-read existence equivalence on the whole signed fiber.
   Its Theorem 6.1 decides the recognized root-to-proper-descendant
   certificate case, retaining every other constraint. Theorems 14.1
   and 22.1 decide respectively its synchronous and constructor-
   elimination families, with bounded original chart selection,
   both original-prefix directions, positive actual consumers and
   finite bad pairs at every requested depth on negative instances.
   Their finite productive-state arguments supply negative stopping
   within those recognized families. General cyclic decorated-
   constructor constraints need not be accepted by these recognizers.
3. [SCR, Theorems 9.2–9.3 and 10.1, Corollary 10.2][SCR] supply sharp
   epoch-four universal positive-epoch one-read transport and its
   raw-count controller normalization. The all-source identity
   restricts to every $D$ by [ABC, Proposition 6.4][ABC]. With
   $M_4=\max(N,4)$ the positive-mode address has length at most
   $|p|+M_4-1$; a zero-entry service retains its zero-epoch actions
   until the reply-dependent first simulated update. This preserves
   raw counts, with an additive length bound, and may add actual
   updates to a comparator that would halt early. It is not joint
   nonexpansive dominance.
4. [JRF, Lemma 2.2 and Theorem 3.1][JRF] supply the separate all-source
   nonexpansive cap at $M=\max(N,5)$. On each same $u$, its capped
   service has $q'=q$, $a'=\min(a,M-N)$ and $\ell'\le\ell$.
   Its cleanup and shortest-old-class-occurrence results also restrict
   to the complete signed fiber, as stated in ABC Proposition 6.4.
   JRF Theorems 4.3, 5.3 and 7.1 give effective exact feasibility,
   the Pareto basis and separate rational weighted minimax on the
   literal-history fibers for which its GB and matched WS2S suppliers
   are proved. Those logical suppliers do not thereby express arbitrary
   coupled signed morphic equations.
5. [AOF, Assumption 1.1 and Theorems 3.1, 4.1, 5.1][AOF] require an
   actually acquired positive record $(n,\varepsilon,m,p,=)$ with
   $p\ne\varepsilon$, allowing exchange of its endpoints. All additional
   records and old row constraints remain arbitrary and jointly imposed.
   Its nonempty fiber is exactly $\{T_j:j\in S\}$ for an effectively
   computed finite/cofinite $S$, and its authentic entry satisfies
   $N\ge1$. It gives an entry-static sourcewise simulation with
   $q'=q$, $a'=0$ and $\ell'\le\ell$. In its finite-output cases,
   finite representatives and a finite address menu have both proved
   operational directions on the entire original fiber, including
   the infinite tail. The resulting finite family is cofinal against
   every original comparator for the separate worst-coordinate and
   same-source weighted objectives. Strictly decreasing surviving
   representative sets bound the decision depth. Its theorem therefore
   computes the exact attained Pareto basis and every rational weighted
   optimum, including zero weights; this is stronger than merely
   selecting representatives with the same target values.

In item 5 finite output means finite $S$ or complete $Q$ in AOF's sense
that every infinite address ray meets a cut. If $S$ is cofinite and
$Q$ is incomplete, AOF proves no finite joint upper budget, and proves
weighted value $\infty$ when $\lambda_q>0$ or $\lambda_\ell>0$, and
zero otherwise; a sourcewise terminating entry-static service realizes
the stated extended values. These conclusions cover the recognized
certificate fiber only. They leave the synchronous and constructor-
elimination families' more general exact optimization questions outside
that certificate unchanged.

The supplier identifications have their original types. The native
source in [SourceTransportCentralizer][CENTRALIZER] is
$\alpha=\mathtt{of\ true}$, $\beta=\mathtt{of\ false}$,
pairing $=\mathtt{FreeMagma.mul}$ and $\rho=\mathtt{substitution}$.
Its centralizer declaration concerns that free source action.
[SourceTreeEncoding][ENCODING]'s $\mathtt{source\_code\_equiv}$ is an
encoding into its specified hereditary-finite grammar. The pinned
[mathlib free magma][FREE] supplies its free constructor algebra. None
of these types specifies KR definability of the recursively defined
normal domain, so none replaces the domain formula excluded above.
The source-relative inference here is the finite-expression obstruction,
not a new encoding, orbit classification or operational simulation.

**Definition 5.4 (the unrestricted obligations).** For arbitrary data
in Definition 5.1, write $\operatorname{PrefDet}(D,Q,h)$ for

$$
\forall u,v\in D,\quad
 \bigl[\forall |p|\le h,\ r_u(p)=r_v(p)\bigr]
 \ \Longrightarrow\ R_Q(u)=R_Q(v).
\tag{TPO.18}
$$

The unrestricted obligation of [ARH, Definition 9.1][ARH] remains an
effective necessary-and-sufficient decision of
$\exists h\,\operatorname{PrefDet}(D,Q,h)$ with an actual paid
source-total consumer in positive cases and a justified negative
stopping argument. The exact-resource obligation additionally concerns
all arbitrary finite physical address choices and all legal adaptive
serial competitors, with exact sourcewise costs before the suprema in
(TPO.17). A source-language decision for a supplied finite menu does not
decide existence of unbounded-address witnesses. A finite Pareto basis
as a set does not supply an effective stopping rule for finding it.

The domain formula in (TPO.13) is an excluded supplier for one proposed
interpretation of these obligations. Its exclusion neither decides the
obligations negatively nor invalidates any of the recognized positive
and negative decisions in Definition 5.3. An alternative supplier must
supply its own two whole-fiber inclusions and actual paid consumer
correspondence. Preservation of boundedness with multiplicative or
additive resource distortion would not alone identify exact prices.
The identity of sourcewise costs in ABC, the additive raw normalization
in SCR, the sourcewise inequalities in JRF and AOF, and the scoped exact
optimization theorems are distinct mathematical conclusions.

[ABC]: https://github.com/the-omega-institute/trureturing/blob/5acc53740f311d7a854d03f793e4079aa626fe5c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[KR]: https://arxiv.org/html/cs/0408015v1
[ARH]: https://github.com/the-omega-institute/trureturing/blob/ce58f3e6607e4269821891c7ba7e7dad5e8066f9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SCR]: https://github.com/the-omega-institute/trureturing/blob/ebeec0b680e9584d1749fe60fefb98ee1044300a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md
[JRF]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[AOF]: https://github.com/the-omega-institute/trureturing/blob/fee3e2b8ff28d5048af2e03cfd83ef522a30365b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[CENTRALIZER]: https://github.com/the-omega-institute/trureturing/blob/5acc53740f311d7a854d03f793e4079aa626fe5c/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[ENCODING]: https://github.com/the-omega-institute/trureturing/blob/5acc53740f311d7a854d03f793e4079aa626fe5c/D5/S0/History/Spacetime/SourceTreeEncoding.lean
[FREE]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Free.lean

## 追加锚（本行以下为增补区）
