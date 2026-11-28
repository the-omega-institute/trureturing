---
slug: mekera-somer-yesil-matrix-arc-ranks
bibkey: mekerasomeryesil2026matrixarcranks
doi: 10.48550/arXiv.2608.09243
url: https://arxiv.org/html/2608.09243v2#S7.p2.1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.arc
---

# Rank tests for ordered annihilator-digraph arcs

## Problem

Mekera, Somer and Yeşil ask in §7, p. 17, how the arcs of
\(\overrightarrow{\mathrm{AG}}(M_n(F))\) can be characterized in terms
of matrix ranks.
[Versioned question](https://arxiv.org/html/2608.09243v2#S7.p2.1) ·
[Reading note](../Library/Semigroups/mekerasomeryesil2026matrixarcranks.md)

## Motivation

In the full matrix ring over \(F\), the vertices are exactly the nonzero
singular matrices. Definition 4.1 tests an ordered pair of distinct
vertices by asking for an annihilator of their product on one side that
annihilates neither endpoint on that same side.
[Definition 4.1](https://arxiv.org/html/2608.09243v2#S4.Thmtheorem1)

## Gap

Fix any field \(F\), an integer \(n\ge 2\), and distinct nonzero
singular \(A,B\in M_n(F)\). Write \(C=AB\) and \(k=\operatorname{rank} C\).
The two witness conditions must give the two branches of the criterion
with the indicated block orientations.

\[
 A\to B \quad\Longleftrightarrow\quad
 \big(k<\operatorname{rank}A\ \land\ k<\operatorname{rank}[C\mid B]\big)
 \ \lor\
 \left(k<\operatorname{rank}B\ \land\
 k<\operatorname{rank}\begin{bmatrix}C\\ A\end{bmatrix}\right).
\]

## Route

A nonzero matrix with determinant zero has a nonzero kernel vector.
Placing that vector in a column gives a nonzero right annihilator.
Invertibility excludes both kinds of nonzero annihilators.

For the right branch, the columns of any right annihilator of \(C\) lie
in \(\ker C\). A valid witness exists exactly when \(\ker C\) is contained
in neither \(\ker A\) nor \(\ker B\). If two vectors avoid the two endpoint
kernels separately and each belongs to the other kernel, their sum avoids
both. A matrix with a column equal to a common avoiding vector supplies
the witness. Since \(\ker B\subseteq\ker C\) and the vertical block has
kernel \(\ker C\cap\ker A\), rank–nullity gives the right branch. Apply that
argument to \((B^{\mathsf T},A^{\mathsf T})\) for the left branch.

## Falsifier

A pair satisfying the endpoint conditions would falsify the criterion
if its ordered witness test and the displayed disjunction disagreed.
The reverse direction is a separate arc test with the product \(BA\).

## Evidence

The Lean theorem uses the repository's exact Definition 4.1 predicates
and the two matrix annihilator equivalences. The statement ranges over
fields of arbitrary characteristic and cardinality.
[Lean result](../D5/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration.lean) ·
[Preregistration #35243](https://github.com/the-omega-institute/trureturing/issues/35243)

## Triage

The frozen theorem answers the rank question for every field and every
finite dimension with distinct vertices.
[Frozen criterion](../Blueprint/D5/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration.md)

### What the settlement shows

The block ranks detect the strict inclusions that let a single witness
avoid both endpoint annihilators. The subspace argument also works over
\(\mathbb F_2\). In dimension zero the matrix ring has only its zero element. In dimension
one the full matrix ring is a field. Both vertex sets are empty. The criterion concerns the annihilator digraph of
Definition 4.1. The paper's comparisons with extended digraphs are
separate questions.

## ASSUMED-UNVERIFIED

The bounded literature search documented in the preregistration found
no exact earlier rank criterion for Definition 4.1. Complete index
coverage and worldwide priority remain unverified.
[Search scope and limitations](https://github.com/the-omega-institute/trureturing/issues/35243)
