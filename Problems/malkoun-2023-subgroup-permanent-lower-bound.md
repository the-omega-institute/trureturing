---
slug: malkoun-2023-subgroup-permanent-lower-bound
bibkey: malkoun2023cousins
doi: null
url: https://mathoverflow.net/questions/456248/do-these-cousins-of-permanents-satisfy-the-following-inequality
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.result
---

# Malkoun: the unrestricted subgroup permanent lower bound

## Problem

Malkoun, *Do these cousins of permanents satisfy the following inequality?*,
MathOverflow question 456248, revision 8,
`382F6B28-9E4F-456B-9254-E0A041A674B5`.
The [source note](../Library/QuadraticForms/malkoun2023cousins.md) gives the identity,
attribution, license and bounded literature comparison.

> Let $H$ denote an $n$ by $n$ hermitian positive semidefinite matrix. Let $G$
> and $K$ be two subgroups of the symmetric group $\Sigma_n$. Define
> $f_{G,K}(H)=\sum_{(\sigma,\tau)\in G\times K}\prod_{i=1}^n
> h_{\sigma(i),\tau(i)}$. Does there exist a positive constant $c(n,G,K)$
> depending on $n$, $G$ and $K$ such that
> $\Re(f_{G,K}(H))\geq c(n,G,K)\prod_{i=1}^n h_{ii}$?

The complete quantifier order is

$$
\forall n\in\mathbb N\ \forall G,K\leq\operatorname{Sym}(n)\quad
\exists c\in\mathbb R\quad c>0\ \land\
\forall H\in M_n(\mathbb C),\quad
 (H=H^*\land H\succeq0)\Longrightarrow
 c\prod_i\Re(h_{ii})\leq\Re(f_{G,K}(H)).
$$

`claim` has this proposition as its definition and `result` has type `¬ claim`.
Native index $i:\mathrm{Fin}(n)$ corresponds to source label $i+1$; every
permutation acts on that same index set. `crossSum` sums over the actual
subgroup types, without normalization. No Young-subgroup, rank, entry-sign
or strictly positive diagonal condition is added to the universal assertion.
`diagonal_product_eq_real` supplies the Hermitian real-diagonal bridge.

## Motivation

The source relates the expression to two subgroup symmetrizations of a pure
tensor and to graph-associated functions. A lower bound would extend the
positivity behind familiar permanent inequalities to a two-sided subgroup
cross-sum. Positivity of a Gram matrix by itself does not imply positivity
of a cross-sum over two different subgroup orbits.

## Gap

The unrestricted question concerns actual permutation subgroups and matrices
in the complex PSD cone. Negativity for arbitrary operators on a representation
space leaves a realization gap. The counterexample below closes that gap with
an explicit square Gram matrix in the original matrix domain.

## Route

Set $n=7$ and

$$
G=\langle(1\ 2\ 5\ 6\ 4\ 3\ 7)\rangle,\qquad
K=\langle(1\ 2\ 7\ 5\ 6\ 4\ 3)\rangle.
$$

In zero-based array form the generators are $(1,4,6,2,5,3,0)$ and
$(1,6,0,2,5,3,4)$. Both have order seven. Their seven powers therefore
enumerate the actual subgroups bijectively, using the pinned
`finEquivZPowers` equivalence.

Let $V$ have columns $(1,2),(3,2),(1,-2),(3,2),(1,0),(1,-3),(3,-2)$ and
embed its integer entries in $\mathbb C$. Then

$$
H=V^*V=
\begin{pmatrix}
5&7&-3&7&1&-5&-1\\
7&13&-1&13&3&-3&5\\
-3&-1&5&-1&1&7&7\\
7&13&-1&13&3&-3&5\\
1&3&1&3&1&1&3\\
-5&-3&7&-3&1&10&9\\
-1&5&7&5&3&9&13
\end{pmatrix}.
$$

This is an actual $7$ by $7$ complex Hermitian positive semidefinite matrix,
by `Matrix.posSemidef_conjTranspose_mul_self`. A rectangular Gram factor
is sufficient: the source condition is on the resulting square matrix.

## Falsifier

The diagonal is $(5,13,5,13,1,10,13)$ and has product $549250>0$.
For powers $g^a$ and $k^b$, with $a,b=0,\ldots,6$, the seven row sums of
the complete $49$-term sum are

$$
(568948,-90288,-206028,-182088,-90000,-100172,75684).
$$

Their sum is $-23944$. Consequently every $c>0$ would require
$549250c\leq-23944$, which is impossible. The same fixed matrix works
for every positive $c$ for the fixed pair $G,K$.

## Evidence

`D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.result` is the
literal negation of the full claim. The native proof uses `Subgroup.zpowers`
of actual `Equiv.Perm (Fin 7)` values, proves both generator orders, reindexes
the complete subgroup sums by `finEquivZPowers`, and evaluates the resulting
complex products exactly. The real diagonal equality is consumed in the
diagonal-product calculation. The proof uses the pinned Gram-positivity
supplier, rather than a positive-semidefiniteness assumption about the witness.

## Triage

**PROVED — Refutation of the complete main arbitrary-subgroup assertion.**
The native result proves `¬ claim` using the displayed matrix and subgroups.

**COMPUTED — Failure of the additional unrestricted strict-positivity assertion
on the same family.** The displayed matrix has positive diagonal and negative
real cross-sum. The obstruction occurs already at the sign of the full
cross-sum: positive semidefiniteness and positive diagonal do not ensure its
nonnegativity for two arbitrary subgroups. A smaller positive constant cannot
repair this sign failure. This consequence is the same counterexample, with
no separate problem settlement claimed.

**OPEN — The Young-subgroup question, including the author's rank-two
restriction.** The two cyclic subgroups here are not the specified products
of symmetric groups on disjoint subsets.

**OPEN — The separate trivial-subgroup question.** Both subgroups in this
counterexample are nontrivial.

## ASSUMED-UNVERIFIED

The literature check has the finite scope stated in the source note. No
worldwide-priority or exhaustive absence claim follows. The tensor formulation
and arbitrary-operator follow-up are not used as substitutes for the original
matrix domain. Independent review, repository integration and post-integration
verification are distinct obligations from this mathematical statement.
