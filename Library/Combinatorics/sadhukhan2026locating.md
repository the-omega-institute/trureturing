---
bibkey: sadhukhan2026locating
authors: Arpan Sadhukhan; Sagnik Sen
year: 2026
title: "Locating a Seymour vertex in oriented graphs having minimum outdegree at most 7"
doi: null
url: https://arxiv.org/abs/2606.30588v2
claim: "Theorem 1.2 constructs, for all positive integers q and r, an oriented graph with minimum outdegree 3r+2 and exactly q minimum-outdegree vertices, such that every Seymour vertex has directed distance greater than r-1 from every minimum-outdegree vertex."
strata_touched:
  - D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods
  - D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant
  - D5/S3/Combinatorics/Graph/SeymourSharpness/Family
license: citation-only
triage: anchor
---

# Directed distance from minimum roots to Seymour vertices

## Verified locator

URL: https://arxiv.org/abs/2606.30588v2

Version: arXiv:2606.30588v2. Theorem 1.2 states the all-positive-parameter
sharpness construction. Section 3 gives its block sizes, adjacency relation,
first and exact second neighborhood counts, and distance lower bound.
The primary TeX source has SHA-256
`401a2d84b5f1a7fb9a1feded5b269cea318251acdf990bec65d2bca301612666`.

## Construction and exact attainment

Write delta = 3r+2. There are r+3 blocks of sizes
`q, delta, delta-1, ..., delta-r, 2delta+1`. Block zero is independent.
Every other block of size n carries the circulant on ZMod n with offsets
from one through floor((n-1)/2). Complete cross edges follow the directed
cycle of blocks, with no other cross edges.

The internal first and exact second degrees are both floor((n-1)/2).
Consequently a vertex of block i has global degrees
`t_i+n_(i+1)` and `t_i+n_(i+2)`, with cyclic subscripts and t_0=0.
Precisely block zero has outdegree delta. For 1<=i<=r, the degree is
`floor((delta-i)/2)+delta-i`, which exceeds delta. The final two block
degrees are `r+2delta+1` and `delta+q`.

Blocks with index less than r are not Seymour, since their exact second
degree is one less than their first degree. Block r is Seymour because
its second successor block has size 2delta+1. Every edge stays in its
block or advances one block. Thus no walk shorter than r reaches a
Seymour vertex from block zero. Successive complete cross edges through
nonempty blocks give a length-r walk to block r from every minimum root.
This establishes exact attainment in the same constructed graph.

## Formal scope and attribution

This is known substantive mathematics, not a resolution of the proposed
universal upper bound for arbitrary oriented graphs. The exact equality
uses the source's block r in addition to its stated lower bound.
The formal family also includes r=0, where each minimum root is already
Seymour and its zero-length walk gives attainment. Positivity of q
ensures finite cluster carriers and a positive number of minimum roots.
Orientation alone does not require positivity of q.

The formal exact second neighborhood excludes the root and all its first
outneighbors and requires an actual two-edge witness. Both walk bounds
quantify over the same relation and the same minimum root. A proved
finite reindexing gives the final relation on Fin n. No source text is
vendored, and no literature novelty claim is made.
