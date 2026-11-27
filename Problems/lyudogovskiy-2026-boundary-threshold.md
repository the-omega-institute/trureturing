---
slug: lyudogovskiy-2026-boundary-threshold
bibkey: lyudogovskiy2026simplex
doi: 10.48550/arXiv.2603.23228
url: https://arxiv.org/html/2603.23228v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary.boundary_result
---

# Lyudogovskiy's boundary-threshold question

## Problem

Fedor B. Lyudogovskiy, *Simplex Stratification and Phase Boundaries in the
Partition Graph*, arXiv:2603.23228v1, printed p. 12. The displayed mathematics
in the following quotation is transcribed in LaTeX. [Source PDF](https://arxiv.org/pdf/2603.23228v1#page=12)

> **Problem 6.3 (Boundary thresholds).** Determine the boundary threshold function
>
> $\tau_{\partial}(r)=\min\{n:\partial_{r,r+1}(n)\ne\emptyset\}$.
>
> In particular, does one have
>
> $\tau_{\partial}(r)=\tau(r+1)\qquad(r\ge 1)$?
>
> That is, does every new simplex layer first appear already in direct contact with the previous one?

## Motivation

The vertices are native integer partitions of a positive size. Each edge
transfers one unit and reorders the parts. The local dimension is the largest
clique size through a vertex minus one. The layers use exact dimensions.
Proposition 4.3 makes boundary nonemptiness equivalent to an interface edge.

## Gap

For every natural r at least one, the Lean statement gives attainment and
leastness among positive sizes with an edge from local dimension r to r+1.
The higher-layer threshold formula identifies the least size
`triangular (r+1) + 1` with the source's $\tau(r+1)$. For r=0, each edge
supplies a two-vertex clique, so the defining set is empty and the source's
minimum is undefined under Definition 4.5.

## Route

Delete the bottom singleton from the top-row extension of the staircase of
rank r+1. Inserting at the r+1 selected addable corners yields a clique by
the transfer/intersection equivalence. Restoring the singleton gives the
upper endpoint in the first-occurrence family. Alternatively extending the
top row gives a lower endpoint outside that family. Its clique and the
maximum bound force dimension r. At any admissible positive size the upper
endpoint belongs to the exact layer r+1, which gives the required lower
bound on size.

## Falsifier

An adjacent pair of the stipulated dimensions at a smaller positive size,
or the absence of such a pair at the first size of layer r+1, would refute
the formula.

## Evidence

[Formal source](../D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary.lean)
and [prospective issue](https://github.com/the-omega-institute/trureturing/issues/34731).

## Triage

The Lean theorem proves the displayed least-size formula over the complete
positive range. The source note is shared with Problems 6.1 and 6.2.
[Library note](../Library/FiniteGeometry/lyudogovskiy2026simplex.md)

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive literature coverage remain unverified.
