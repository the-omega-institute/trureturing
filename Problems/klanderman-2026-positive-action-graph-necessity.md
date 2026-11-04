---
slug: klanderman-2026-positive-action-graph-necessity
bibkey: klanderman2026generalizedactiongraphs
doi: 10.46787/pump.v9i.6304
url: https://journals.calstate.edu/pump/article/view/6304
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity.result
---

# Strictly positive coefficients are not necessary for generalized action graphs

## Problem

S. Klanderman, K. McDicken and A. Tebbe, *Conditions for Building Generalized
Action Graphs From Sequences*, The PUMP Journal of Undergraduate Research
9 (2026), 158–179, DOI 10.46787/pump.v9i.6304, Section 4, page 178, asks:

> Another open question is whether the hypotheses of Theorem 1.1 are in fact necessary conditions for generalized action graphs to exist.

This dossier anchors exactly that question, with the strict positivity in
Theorem 1.1. The theorem assumes positive integers $s_n$ for every $n\ge0$
and $z_i$ for every $i\ge1$, with $s_0=1$ and

$$
s_n=\sum_{i=1}^{n}z_i s_{n-i}\qquad(n\ge1).
$$

The necessity assertion quantifies every positive integer sequence and the
existence of one entire family of generalized action graphs, and concludes
the normalization and existence of coefficients satisfying all these
conditions. The value $z_0$ is irrelevant and unrestricted. The earlier
arXiv:2507.22861v1, Section 6, is an alias of this question: its Definition
4.1 and Theorem 2.1 correspond to journal Definition 1.1 and Theorem 1.1.
It is not a second target. Preregistration is
[#23113](https://github.com/the-omega-institute/trureturing/issues/23113).

Definition 1.1, pages 158 and 172, gives the full source model:

> The sequence Gn of generalized action graphs for a particular sequence sn of positive integers is a sequence of directed, labeled, rooted trees such that:
> Axiom 1 Define G0 as the graph with s0 vertices labeled 0 and no edges. Construct Gn from Gn−1 by adding sn new vertices, which are each labeled n.
> Axiom 2 For vertex v in Gn, the subtree of Gn with root v is isomorphic to some Gk such that k ≤ n.
> Axiom 3 All leaves in the graph Gn have label n.

The paragraph following the repeated definition on page 172 specifies:

> Note that subtree of G with root v here means the subgraph of G consisting of all descendants of v and edges between them in G.

Section 3.1, page 172, specifies the label convention:

> Note that when we consider isomorphism in generalized action graphs, the labels on the vertices may be shifted, but the underlying structure of the graphs are the same.

## Motivation

Theorem 1.1 supplies sufficient sequence conditions for constructing the
whole graph family. Its converse would characterize which positive
sequences admit such graphs. The distinction between strictly positive
coefficients and zero multiplicities matters: the graph axioms do not
require the root to have a neighbor of every positive label. Establishing
the distinction requires an actual family satisfying every graph axiom,
rather than a vertex-count recurrence alone.

## Gap

The published Section 4 poses the converse without an answer. The bounded
source, version and citation screen recorded with #23113 found no complete
earlier settlement. Failed or rate-limited sources provide no negative
evidence. This is a Tier 1 recent, explicitly posed question; it is not a
claim of exhaustive priority or a long-standing difficult problem.

The distinct Caldwell et al. arXiv:2507.22719 Conjecture 5.6 concerns the
super Catalan action-graph n-table identity, registered in #14721 and
#14747. Neither that identity nor the journal's sufficient construction
settles this universal necessity assertion.

## Route

Set $s_n=1$ for every $n\ge0$. For every stage $n$, take the vertex set
$V_n=\operatorname{Fin}(n+1)$, root $0$, label $\ell_n(i)=i$, and the
directed edges $i\to i+1$. Retain old vertices by the natural inclusion
$V_n\hookrightarrow V_{n+1}$. This is one family for all stages, including
the singleton stage $n=0$.

The full formal graph predicate expresses the source clauses as follows:

1. Each carrier is finite, its underlying simple graph is a tree, every
   vertex is actually reachable from the root, and there is no nonempty
   directed closed walk. For these paths the underlying graph is
   `SimpleGraph.pathGraph (n+1)`, reachability is $\le$, and nonempty
   reachability is $<$.
2. The initial graph has exactly $s_0=1$ vertices, all labeled zero, and
   no edges. Every inclusion preserves the root, labels, and both
   directions of the adjacency equivalence on retained vertices. Its
   complement consists exactly of the new last vertex, has cardinality
   $s_{n+1}=1$, and that vertex has label $n+1$.
3. At every $i\in V_n$, the descendant carrier is exactly
   $\{j\in V_n:i\le j\}$, including $i$, with all and only the induced
   directed edges. Put $k=n-i\le n$. Translation $j\mapsto i+j$ is a
   bijection from $V_k$ to that carrier, preserves and reflects adjacency,
   sends the root to $i$, and shifts every label by the single natural
   number $i$. The formal map is a rooted `RelIso`, not a count surrogate.
   The case $i=n$ is the singleton descendant subtree, isomorphic to
   $G_0$; the case $n=0$ uses the same construction.
4. A leaf means a vertex with no outgoing edge. The only leaf of $G_n$
   is its last vertex $n$, so every leaf has label $n$.

If strictly positive $z_i$ satisfied all the convolution equations, the
equation at $n=1$ would give $1=z_1$, and the equation at $n=2$ would give
$1=z_1+z_2$. Thus $z_2=0$, contradicting $z_2>0$. The complete legal graph
family therefore refutes the closed universal necessity assertion.

## Falsifier

A source restriction excluding the constant positive sequence, a graph
axiom imposing strictly positive root multiplicities at every label, or a
label convention forbidding the quoted uniform shifts would invalidate
this source correspondence. Failure of any actual tree, reachability,
acyclicity, retention, descendant-isomorphism or leaf clause would
invalidate the family. The source definition imposes none of the first
three restrictions, and the formal proof checks all the graph clauses
for every stage. A prior complete settlement would affect the bounded
literature qualification, rather than the mathematical contradiction.

## Evidence

The formal source is
`D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity.lean`.
`IsGeneralizedActionGraph` carries the entire model above; `claim` is a
closed proposition; the private `path_family_legal` proves the full
infinite path family legal and is consumed by `result`. The sole public
theorem `result` has literal type `Not claim` and no free parameters.
Its accepted axiom closure is contained in
`{Classical.choice, Quot.sound, propext}`. The host module is a canonical
frozen-state member. The Blueprint expands every model clause and the
grouped negation of the entire claim; its Refuted binding names only
this theorem and this dossier.

Both authored theorems have `proof_shape: bind-only`: they compose pinned
Mathlib graph, order, finite-equivalence and sum owners with the explicit
path data and normalization. Their admission basis is the external
`open-problem-resolution` of #23113; no escape witness or additional
content theorem is claimed. The helper's actual consumer is `result`.
The definitions are consumed on that same proof path. There are no
direct frozen D5 dependencies, no separate public audit target beyond
the exempt designated refutation result, and no digestion atom for this
uncovered source. No experiment program or finite numerical surrogate
is needed for this all-stage proof.

The canonical Library note records the journal DOI, URL, exact locators,
version correspondence and source quotations. The result is a repository
derivation acknowledging that source; the authors pose the question and
are not attributed this refutation.

## Triage

- **Proved in Lean:** the entire directed-path family satisfies every
  original graph axiom, while its sequence cannot have strictly positive
  coefficients in all the convolution equations. This is the single
  anchored refutation, including every $n\ge0$.
- **Mechanism established by the refutation:** descendant self-similarity
  and terminal leaf labels permit a path; neither condition enforces a
  positive number of root neighbors of every label. The first two
  convolution equations expose the missing strict positivity.
- **Source theorem retained:** the sufficient direction of Theorem 1.1
  is unaffected. Refuting its converse does not invalidate its construction
  or independently established sequence examples.
- **Unsettled:** the universal necessity question with nonnegative
  coefficients, stronger graph axioms, and other converse variants. The
  present result supplies no new all-sequence nonnegative conclusion.
  Those variants would require separate statements and qualification.

## ASSUMED-UNVERIFIED

The bounded literature screen does not certify exhaustive worldwide
novelty, priority, or the latest state of every citation and version.
Those external states have not been freshly re-queried for this dossier.
The mathematical conclusion is conditional on the explicitly quoted
source conventions, whose correspondence is a content-review obligation
beyond Lean's kernel. A recorded Refuted binding is not merge, required-CI
or independent final-review clearance, and supplies no delivery credit
before normal integration and verification of the first dev push.
