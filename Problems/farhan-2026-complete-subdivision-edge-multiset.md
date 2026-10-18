---
slug: farhan-2026-complete-subdivision-edge-multiset
bibkey: farhan2026multiset
doi: null
url: https://arxiv.org/pdf/2607.10311v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.result
---

# Once-subdivided complete graphs have infinite edge multiset dimension

## Problem

Problem 24, section 7.4, printed page 27 of the versioned source asks whether the edge
multiset dimension of K_n^1 is infinity for every integer n at least three. The definition
on printed page 21 inserts one midpoint into every complete-graph edge. Section 6.1 on
printed page 20 uses minimum actual shortest endpoint distances and arbitrary landmark
subsets of the full vertex set, including originals and midpoints. Profiles are multisets
with multiplicity; infinity means that no resolving subset exists.

## Motivation

`D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.result` gives the full
affirmative conclusion: for every n at least three and every arbitrary landmark set,
two distinct actual graph edges have equal distance multisets, and the extended-natural
edge multiset dimension is top.

## Gap

The source's diameter-two obstruction covers n=3 but leaves n at least four, where a
disjoint midpoint has edge distance three. The full landmark domain requires a free
diagonal in the selection matrix, rather than a simple-graph adjacency convention.

## Route

Exact shortest-distance histograms force distinct augmented selected degrees for any
hypothetical resolving set. The symmetric binary selection matrix has unrestricted
diagonal. Complement and row-rank permutation reduce it to a proved staircase.
Explicit even and odd incidence pairs have identical four-bin histograms, contradicting
resolution. The odd case includes n=3; arbitrary sets are finite because the full vertex
type is finite. All bridges are proved in the eight native modules.

## Falsifier

An n at least three and a subset of the full subdivided vertex set whose actual
minimum-shortest-endpoint distance multisets are pairwise distinct on all graph edges.

## Evidence

The native endpoint and its graph, reachability, distance, histogram, selection,
complement, collision and staircase dependencies carry Lean proofs. The source endpoint states both
the collision on actual edges and the resulting infinite dimension.

## Triage

`theorem`: the formal mathematical conclusion is affirmative for the entire printed
Problem 24 domain. This dossier makes no repository acceptance or solved-count claim.

## ASSUMED-UNVERIFIED

Source-open is verified in the versioned source. The bounded literature scope is the
source, arXiv:2608.09983v1, section 7.4 of arXiv:2607.08128v1 and the released repository
candidate search. Worldwide current openness and priority remain unverified.
