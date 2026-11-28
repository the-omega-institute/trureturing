---
slug: alsinai-ahmed-sunlet-detour
bibkey: alsinai2026detour
doi: 10.48550/arXiv.2611.26653
url: https://arxiv.org/abs/2611.26653v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_detour_numbers
---

# The detour different-distance numbers of a sunlet

## Problem

Ammar Alsinai and Hanan Ahmed ask the following in *Detour different-distance
sets in graphs*, §4, Problem 4.3, page 13. [Pinned paper](https://arxiv.org/pdf/2611.26653v1)

> Determine ddD for lollipops, barbells and tadpoles, and both numbers for grids, sunlets, snakes and generalized Petersen graphs.

The sunlet clause asks for both extrema. For every integer $n\ge 4$, the
answer for the sunlet $C_n\circ K_1$ is

$$
\mathrm{dd}_D(C_n\circ K_1)=\mathrm{DD}_D(C_n\circ K_1)=2.
$$

The sunlet has one leaf at each vertex of the cycle. Detour distance is the
maximum edge length of a simple path between the given vertices, with zero
on the diagonal. A DDD set is a nonempty proper vertex set such that every
outside vertex has distinct detour distances to distinct members.
Definition 1.1 takes the minimum and maximum cardinalities over the same
family of inclusion-maximal DDD sets.

## Motivation

The two numbers measure the range of sizes of maximal DDD sets. Lemma 3.4
supplies a DDD pair at every cycle vertex by pairing it with its own leaf.

## Gap

The source already gives both numbers for $n=3$ in Theorem 2.14(i) because
$C_3=K_3$ and $K_1+K_1=K_2$ are Hamiltonian-connected. For $n\ge 4$,
every Hamiltonian path in $C_n$ has adjacent endpoints, so $C_n$ fails
that hypothesis. The settlement concerns the sunlet clause alone.
[Preregistration #35174](https://github.com/the-omega-institute/trureturing/issues/35174)

## Route

At distinct indices, the detour uses the longer cycle arc and one edge for
each leaf endpoint. The proof of Theorem 2.1 gives the bare-cycle formula,
and Lemma 3.3 gives the pendant-block contribution. At a single index, the
diagonal distance is zero and the core–leaf distance is one.

## Falsifier

An inclusion-maximal DDD singleton or a proper DDD set of size at least
three would refute the result. Finiteness lets any DDD set extend to an
inclusion-maximal one.

## Evidence

`D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_isGreatest_pathLength_of_index_ne`
proves attainment and a universal upper bound for native simple-path
lengths at distinct indices for every $n\ge 3$ and both endpoint heights.

`D5/S3/Combinatorics/Graph/Sunlet/DetourPath.sunlet_detour_numbers`
proves both extrema for every $n\ge 4$ in the pinned Mathlib backend.

The §3.9 audits remain unfinished. The path theorem lacks accepted
dependent parameter packing and a binding to the scoped native walk length.
The extrema theorem lacks an accepted reconstruction of both equalities on
the same maximal-order set under $n\ge 4$.
[Theorem-specific diagnostics](https://github.com/the-omega-institute/trureturing/issues/35174#issuecomment-7235811241)

## Triage

### What the settlement shows

A detour tie forces both vertices at the observing index into the set. A
two-color argument forces a complete core–leaf pair from three selected
vertices. Matching the color of a selected vertex at another index forces
a second complete pair. If the two closest complete indices are
nonadjacent, an interior vertex near the midpoint of their shortest arc
forces a closer complete pair. Adjacent complete indices force every
vertex, contradicting properness. This bounds every DDD set by two.
Each singleton extends to its core–leaf pair, and the order bound makes
each such pair maximal. Both extrema are attained. The formal result for
$n\ge 4$ and the source's triangle case together give both values for
every cycle length of a sunlet.

## ASSUMED-UNVERIFIED

Priority beyond the literature searched for the preregistration remains
unverified. [Literature search scope](https://github.com/the-omega-institute/trureturing/issues/35174)
