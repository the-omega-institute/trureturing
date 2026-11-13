---
slug: lyudogovskiy-2026-first-occurrence-family
bibkey: lyudogovskiy2026simplex
doi: null
url: https://arxiv.org/html/2603.23228v1
triage: open
motivation_gids:
  - D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.FirstOccurrenceClaim
---

# Lyudogovskiy's first-occurrence family question

## Problem

Fedor B. Lyudogovskiy, *Simplex Stratification and Phase Boundaries in the
Partition Graph*, arXiv:2603.23228v1, Conjecture 5.2 and Problem 6.2:

Problem 6.2 (First-occurrence families). Assume $r\ge2$, and let
$\delta_r=(r,r-1,\ldots,2,1)$ be the staircase partition of size $r(r+1)/2$.
Is it true that the first-occurrence layer $L_r(\tau(r))$ consists exactly
of the partitions obtained from $\delta_r$ by adding one cell at an
addable corner?

Every r>=2 is retained, including r=2. The target is equality of the
entire finite vertex sets at the literal threshold and at $T_r+1$,
plus exactly r+1 distinct family members. An existence or cardinality
statement alone would not answer the question.

The unresolved proof requires the threshold theorem, both inclusions,
exclusion of top cliques at size $T_r+1$ for every r>=2, the minimal
staircase equality case, and injectivity of distinct addable extensions.

## Motivation

The vertices are all integer partitions of n, represented by native
`Nat.Partition n`. Repeated positive sizes remain repeated occurrences.
The graph transfers one unit between distinct occurrences, including a
virtual zero recipient; it removes a zero remainder and reorders.
Equal resulting partitions are excluded. Local dimension is the largest
actual clique cardinality through the vertex minus one.

## Gap

`FirstOccurrenceClaim` specifies the complete question as a proposition. It is a
claim definition, not a theorem asserting the proposition. Neither whole
question has been proved by this module.

## Route

`UnitTransfer` uses two occurrence slots and a common residual multiset.
`graph` is its simple graph. `cliques`, `localDimension`, `layer`,
`maxDimension`, and `threshold` use actual finite cliques and exact levels.
`staircase` is the finite ideal of cells (i,j) with i+j<r;
`firstFamily` consists of genuine one-cell Young extensions.

The route uses the two-direction transfer/intersection bridge, the
classical star/top classification, corner counts, the triangular support
bound and its staircase equality case, a sharp attaining predecessor,
and exact finite extrema. The classical tools are attributed in the
[source note](../Library/Combinatorics/lyudogovskiy2026simplex.md).
They supply no independent external-problem credit.

## Falsifier

A legal source transfer or clique contradicting the proposed bounds,
an earlier positive exact layer, or a vertex violating the proposed
first-layer equality would refute the corresponding assertion.
The source carrier, virtual zero row and multiplicities must be preserved.

## Evidence

[Formal source](../D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.lean).
[Prospective full-question registration](https://github.com/the-omega-institute/trureturing/issues/30164).
No completed full-question Lean proof, semantic admission, freeze,
reviewed merge or external-problem credit is asserted.

## Triage

Open. arXiv:2603.29988v1 Problem 8.2 is an alias of the same
source event, rather than a second settlement target.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive literature absence are unverified.
The source-specific comparison is bounded to the inspected primary
sources. No proof of either full claim follows from that comparison.
