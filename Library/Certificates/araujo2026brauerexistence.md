---
bibkey: araujo2026brauerexistence
authors: João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon
year: 2026
title: Complete Mappings of Semigroups, Problem 15.11
doi: null
url: https://arxiv.org/abs/2608.25092v1
claim: Problem 15.11 asks which degrees admit complete mappings of the Brauer and partial Brauer monoids.
strata_touched:
  - D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping
license: citation-only
triage: anchor
---

# Complete mappings of Brauer monoids

## Verified locator

Source: https://arxiv.org/abs/2608.25092v1

Section 15, printed page 61, Problem 15.11:

> Classify complete mappings for $\mathcal B_n$ and $\mathcal{PB}_n$. In view
> of the Hall--Paige theorem, the unresolved proper factors are those of ranks
> $2$ and $3$ which occur in the corresponding monoid. Determine also for
> which values of $n$ the whole monoid has a complete mapping.

The existence question is the last sentence. The source does not propose the
answer $n=1$ or $n\ge4$. Classifying every individual complete mapping is a
separate question.

The Introduction defines the object:

> Let $(S,\cdot)$ be a magma, that is, a set with a binary operation. A \emph{complete mapping} of $S$ is a bijection $\alpha\colon S\to S$ such that the mapping $\theta\colon S\to S$ defined by $x\theta = x\cdot x\alpha$ ($x\in S$), called an \emph{orthomorphism}, is also a bijection.
> Here and throughout, our maps act on the right: $x\alpha$ means $\alpha(x)$.

The source refers to East, Mitchell, Ruškuc and Torpey, *Congruence lattices
of finite diagram monoids*, DOI 10.1016/j.aim.2018.05.016,
arXiv:1709.00142v2, §§2.1–2.2, for the diagram monoids. Section 2.2 states:

> Following~\cite{Maz1998},
> the \emph{Brauer} and \emph{partial Brauer monoid} are defined by
> \[
> \B_n = \set{\al\in\P_n}{\text{all blocks of $\al$ have size $2$}} \ANd
> \PB_n = \set{\al\in\P_n}{\text{all blocks of $\al$ have size at most $2$}},
> \]
> respectively.

Section 2.1 defines the partitions and their product as follows:

> Let $n$ be a positive integer.  Throughout the article, we write
> $\bn=\{1,\ldots,n\}$ and $\bn'=\{1',\ldots,n'\}$.  The \emph{partition monoid
> of degree $n$}, denoted $\P_n$, is the monoid of all set partitions of
> $\bn\cup\bn'$ under a product described below.  That is, an element of $\P_n$
> is a set $\al=\{A_1,\ldots,A_k\}$, for some $k$, where the $A_i$ are pairwise
> disjoint nonempty subsets of $\bn\cup\bn'$ whose union is all of $\bn\cup\bn'$;
> the $A_i$ are called the \emph{blocks} of $\al$.
>
> A partition $\al\in\P_n$ may be represented as any graph with vertex set
> $\bn\cup\bn'$ with edges so that the connected components of the
> graph correspond to the blocks of the partition; such a graph is drawn with
> vertices $1,\ldots,n$ on an upper row (increasing from left to right), with
> vertices $1',\ldots,n'$ directly below, and with all edges within the rectangle
> determined by the vertices.

> The product of two partitions $\al,\be\in\P_n$ is defined as follows.  Write
> $\bn''=\{1'',\ldots,n''\}$.  Let $\al^\vee$ be the graph obtained from $\al$ by
> changing the label of each lower vertex $i'$ to~$i''$, and let $\be^\wedge$ be
> the graph obtained from $\be$ by changing the label of each upper vertex~$i$
> to~$i''$.  Consider now the graph $\Pi(\al,\be)$ on the vertex set~$\bn\cup
> \bn'\cup \bn''$ obtained by joining $\al^\vee$ and~$\be^\wedge$ together so
> that each lower vertex $i''$ of $\al^\vee$ is identified with the corresponding
> upper vertex $i''$ of $\be^\wedge$.  We call $\Pi(\al,\be)$ the \emph{product
> graph} of $\al$ and $\be$.  We define $\al\be\in\P_n$ to be the partition
> satisfying the property that $x,y\in\bn\cup\bn'$ belong to the same block of
> $\al\be$ if and only if $x$ and~$y$ are connected by a path in $\Pi(\al,\be)$.
> This process is illustrated in Figure~\ref{fig:P6}.
> %
> The operation is associative and the partition
> $\1=\big\{\{1,1'\},\ldots,\{n,n'\}\big\}$ is the identity element, so $\P_n$ is
> a monoid.
> %
> It is worth noting that even though elements of $\P_n$ naturally correspond to binary relations (indeed, equivalences) on a set of size $2n$, the product on $\P_n$ does not correspond to composition of binary relations.

Lean uses `Bool × Fin n` for the two rows, `Setoid` for partitions,
and `Relation.EqvGen.setoid` for connectedness. Label `i : Fin n` represents
source label `i+1`; `false` and `true` are the unprimed and primed rows.

The half-diagram counts are recorded in Dolinka, East and Gray,
*Motzkin monoids and partial Brauer monoids*, DOI 10.1016/j.jalgebra.2016.09.018,
arXiv:1512.02279v2, Proposition 2.7(ii),(iv).

## Scope

The proposed classification covers every positive degree and every monoid
structure whose multiplication is the stated exterior-connectivity product.
Existence of these source monoids is asserted separately, preventing a
vacuous universal statement. It does not enumerate the complete mappings.

The bounded literature screen in issue #23706 found no settlement of this
existence question in its searched sources. Completeness of that screen and
historical priority remain `ASSUMED-UNVERIFIED`.

The finite checks are in `the-omega-institute/trureturing-experiments`, commit
`99ccaef5cc5ac675599e1843f62f43158f9c6582`, at
`docs/reports/araujo-brauer-complete-mapping/check.py`, SHA-256
`76a2a1e4e3385f7ba79e6ed32bbfcb84e7d110677a6d5c5bc369ee385e508e46`.
The preregistration records exit 0 and `ALL_CHECKS_OK` for
`python3 docs/reports/araujo-brauer-complete-mapping/check.py`.
These checks are finite evidence; they do not establish the unbounded result.
