---
slug: lyudogovskiy-2026-simplex-threshold
bibkey: lyudogovskiy2026simplex
doi: null
url: https://arxiv.org/html/2603.23228v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.threshold_result
---

# Lyudogovskiy's simplex threshold question

## Problem

Fedor B. Lyudogovskiy, *Simplex Stratification and Phase Boundaries in the
Partition Graph*, arXiv:2603.23228v1, Conjecture 5.1 and Problem 6.1:

Problem 6.1 (Threshold formula). Determine the exact threshold function
$\tau(r)=\min\{n:L_r(n)\ne\varnothing\}$. In particular, is it true that
$\tau(r)=1+r(r+1)/2$ for every $r\ge0$? Equivalently, does one have
$\Delta(n)=\max\{r:1+r(r+1)/2\le n\}$?

Every natural r is retained. The threshold is a least positive size of a
nonempty **exact** local-dimension layer, with existence and minimality
explicit. The global maximum formula is a separate conjunct for every
positive n, without a spectrum-contiguity assumption. The endpoints are
$\tau(0)=1$ and $\Delta(1)=0$.

The theorem proves the triangular bound for every actual clique, constructs
an attaining predecessor at every feasible positive size, and uses finite
attainment to obtain exact-layer existence and positive leastness.

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Every partition of positive n | `Nat.Partition n`, `graph` | Repeated occurrences and the virtual zero recipient are retained. |
| Exact local layer | `localDimension`, `layer` | Maximum actual clique dimension through the vertex, then equality to r. |
| Least positive occurrence | `threshold`, `threshold_result` | Every r, including r=0; existence and `IsLeast` are explicit. |
| Global maximum formula | `maxDimension`, `threshold_result` | Every positive n, including n=1; no spectrum-contiguity assumption. |

## Motivation

The vertices are all integer partitions of n, represented by native
`Nat.Partition n`. Repeated positive sizes remain repeated occurrences.
The graph transfers one unit between distinct occurrences, including a
virtual zero recipient; it removes a zero remainder and reorders.
Equal resulting partitions are excluded. Local dimension is the largest
actual clique cardinality through the vertex minus one.

## Gap

`ThresholdClaim` specifies the complete question. The public theorem
`D5.S3.Combinatorics.Partitions.LyudogovskiySimplex.threshold_result` proves it.
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
[Prospective full-question registration](https://github.com/the-omega-institute/trureturing/issues/30163).
The named theorem covers the complete quoted question. Independent semantic
admission and reviewed delivery remain separate obligations. Classical
support lemmas and aliases receive no separate external-problem credit.

## Triage

The full statement is proved in the formal source. arXiv:2603.29988v1 Problem 8.1 is an alias of the same
source event, rather than a second settlement target.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive literature absence are unverified.
The source-specific comparison is bounded to the inspected primary
sources. No proof of either full claim follows from that comparison.
