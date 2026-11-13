---
slug: lyudogovskiy-2026-simplex-threshold
bibkey: lyudogovskiy2026simplex
doi: null
url: https://arxiv.org/html/2603.23228v1
triage: open
motivation_gids:
  - D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.ThresholdClaim
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

The unresolved proof requires the triangular bound for every clique,
an attaining predecessor at every positive size, finite attainment of
local maxima, and exact-layer existence and positive leastness.

## Motivation

The vertices are all integer partitions of n, represented by native
`Nat.Partition n`. Repeated positive sizes remain repeated occurrences.
The graph transfers one unit between distinct occurrences, including a
virtual zero recipient; it removes a zero remainder and reorders.
Equal resulting partitions are excluded. Local dimension is the largest
actual clique cardinality through the vertex minus one.

## Gap

`ThresholdClaim` specifies the complete question as a proposition. It is a
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
[Prospective full-question registration](https://github.com/the-omega-institute/trureturing/issues/30163).
No completed full-question Lean proof, semantic admission, freeze,
reviewed merge or external-problem credit is asserted.

## Triage

Open. arXiv:2603.29988v1 Problem 8.1 is an alias of the same
source event, rather than a second settlement target.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive literature absence are unverified.
The source-specific comparison is bounded to the inspected primary
sources. No proof of either full claim follows from that comparison.
