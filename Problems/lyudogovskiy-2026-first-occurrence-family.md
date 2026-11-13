---
slug: lyudogovskiy-2026-first-occurrence-family
bibkey: lyudogovskiy2026simplex
doi: null
url: https://arxiv.org/html/2603.23228v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.first_occurrence_result
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

The theorem uses the threshold identity and proves both inclusions.
A top clique at this size would contain a staircase of size $T_{r+1}$,
which exceeds $T_r+2$ for every r>=2. A star predecessor contains the
size-$T_r$ staircase and therefore equals it. Distinct addable cells yield
distinct partitions.

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Every r at least two | `FirstOccurrenceClaim` | Includes r=2, with no finite cutoff. |
| Literal first size | `threshold`, `threshold_result` | Connected to $T_r+1$ by the same exact threshold theorem. |
| Entire first-occurrence level | `first_occurrence_result` | Both finite-set inclusions, rather than existence or a count alone. |
| Addable staircase corners | `firstFamily` | Actual one-cell extensions that are Young ideals. |
| Distinct family members | `first_occurrence_result` | Cardinality r+1 at the literal threshold. |

## Motivation

The vertices are all integer partitions of n, represented by native
`Nat.Partition n`. Repeated positive sizes remain repeated occurrences.
The graph transfers one unit between distinct occurrences, including a
virtual zero recipient; it removes a zero remainder and reorders.
Equal resulting partitions are excluded. Local dimension is the largest
actual clique cardinality through the vertex minus one.

## Gap

`FirstOccurrenceClaim` specifies the complete question. The public theorem
`D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.first_occurrence_result` proves it.
The graph is independently defined by actual multiset transfers; the
conclusion is not built into the carrier, adjacency, or clique definitions.

## Route

`UnitTransfer` uses two occurrence slots and a common residual multiset.
`graph` is its simple graph. `cliques`, `localDimension`, `layer`,
`maxDimension`, and `threshold` use actual finite cliques and exact levels.
`staircase` is the finite ideal of cells (i,j) with i+j<r;
`firstFamily` consists of genuine one-cell Young extensions.

The two-direction transfer/intersection bridge relates the source graph to
Young ideals. The classical star/top classification reduces a clique to
addable or removable corners. Sorting their row coordinates gives an
antichain whose lower ideal contains the appropriate staircase; its
triangular size bounds the clique. Enlarging the first row of a staircase
constructs sharp actual cliques at every feasible size. At the first size,
equality forces the predecessor to be the staircase itself. Finite extrema
and injective addable extensions yield the exact thresholds and full families. The classical tools are attributed in the
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
The named theorem covers the complete quoted question. Independent semantic
admission and reviewed delivery remain separate obligations. Classical
support lemmas and aliases receive no separate external-problem credit.

## Triage

The full statement is proved in the formal source. arXiv:2603.29988v1 Problem 8.2 is an alias of the same
source event, rather than a second settlement target.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive literature absence are unverified.
The source-specific comparison is bounded to the inspected primary
sources. No proof of either full claim follows from that comparison.
