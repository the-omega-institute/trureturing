---
slug: lyudogovskiy-2026-dimension-jump
bibkey: lyudogovskiy2026dimensionjump
doi: 10.48550/arXiv.2603.29988
url: https://arxiv.org/abs/2603.29988v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump.result
---

# Lyudogovskiy's local simplex dimension jump

## Problem

Fedor B. Lyudogovskiy, *Simplex Layers and Phase Boundaries in the Partition
Graph*, arXiv:2603.29988v1, submitted 31 Mar 2026, §8.3, Problem 8.4, printed
page 21:

> How much can the local simplex dimension change along a single edge of
> $G_n$? More precisely, what bounds can one place on
> $|\mathrm{dim}_{\mathrm{loc}}(\lambda)-\mathrm{dim}_{\mathrm{loc}}(\mu)|$
> $(\lambda\sim\mu)$?

The result gives the least uniform upper bound over all positive sizes and all
edges. It also gives a symbolic family attaining that bound. Problem 6.4(iii)
of arXiv:2603.23228v1 asks the related uniform-boundedness formulation. [Primary question](https://arxiv.org/html/2603.29988v1#S8.Thmtheorem4) · [Related question](https://arxiv.org/abs/2603.23228v1)

## Motivation

The vertices are the native integer partitions of each positive integer $n$.
An edge transfers one unit between distinct part occurrences, allows a virtual
zero recipient, erases a zero remainder, and reorders. Adjacency excludes equal
endpoints. The local dimension is the maximum cardinality of a clique through
the vertex minus one.

## Gap

The imported local-dimension formula identifies the largest clique through an
individual vertex using star and top capacities. The problem asks for a uniform
comparison of the two local dimensions at the ends of a transfer. The settling
declaration gives the bound $2$ for every such edge and gives, for every
$k\ge4$ at $n=3k-1$, an adjacent pair with decreasing row lists
$[k,k,k-2,1]$ and $[k,k,k-1]$ and exact dimensions $4$ and $2$ respectively.
The integer absolute difference uses the two native local dimensions. The
dossier covers the uniform bound and the attaining family.

## Route

Adjacent diagrams share a one-cell predecessor and successor, so they share
actual cliques obtained by corner extensions and deletions. The proof compares
those sizes against the star and top alternatives at both endpoints. A one-cell
change gains at most one distinct positive row length and loses at most one.
For the displayed family, counting the available corners gives dimension
exactly two at the second endpoint and at least four at the first. The uniform
bound forces equality at the first endpoint.

The star and top mechanism and local-capacity formula are literature inputs.
See §§2.3–2.4 and Theorem 2.1 of the primary paper and Proposition 5.4 of
*Local Morphology of the Partition Graph*. The support-size comparison also
has a precedent in Proposition 3.1 of arXiv:2605.28981v1. The new result is
the sharp comparison across every native edge together with the exact
symbolic attaining family. [Library note](../Library/FiniteGeometry/lyudogovskiy2026dimensionjump.md) · [Local morphology](https://arxiv.org/abs/2603.18696v1) · [Support jumps](https://arxiv.org/abs/2605.28981v1)

## Falsifier

A native edge of positive size with local dimension difference greater than
two would refute the uniform bound. A failure of either exact dimension or of
adjacency at any $k\ge4$ would refute the asserted attaining family.

## Evidence

The direct theorem is
`D5/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump.result`. It uses
`propext`, `Classical.choice`, and `Quot.sound`. The source header records
generality `I` for this partition-graph settlement. The universal clause ranges
over all positive sizes and native edges. [Formal source](../D5/S3/Combinatorics/Partitions/LyudogovskiyDimensionJump.lean) · [Preregistration](https://github.com/the-omega-institute/trureturing/issues/34730)
Verified locator: https://arxiv.org/html/2603.29988v1#S8.Thmtheorem4

## Triage

The theorem gives a sharp uniform bound. The earlier boundedness question
is a related formulation of the same comparison.

## ASSUMED-UNVERIFIED

The source comparison has bounded literature scope. Worldwide priority is
unverified.
