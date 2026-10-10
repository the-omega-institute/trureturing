---
slug: pham-vu-2026-well-covered-powers-diameter
bibkey: phamvu2026wellcovered
doi: 10.48550/arXiv.2610.09300
url: https://arxiv.org/abs/2610.09300v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.result
---

# Pham–Vu Question 3.9: diameter of graphs with well-covered powers

## Problem

My Hanh Pham and Thanh Vu, *On graphs whose powers are well-covered*,
arXiv:2610.09300v1 (7 October 2026), Question 3.9:

> Question 3.9. Let G be a simple connected graph such that G^d is well-covered for all d ≥ 1. Is it true that diam(G) ≤ 3? Furthermore, if diam(G) = 3, are there only finitely many such graphs without true twins?

Definition 2.2 puts an edge between distinct vertices of G^d precisely when
their G-distance is at most d. Definition 2.3 defines well-coveredness by equal
cardinalities of minimal vertex covers. Complementation identifies these
with maximal independent sets. Corollary 3.5 defines true twins as adjacent
vertices with equal closed neighbourhoods.

This dossier settles the first clause. The closed Lean `claim` quantifies over
finite vertex types, simple graphs, their decidable adjacency, connectedness,
and every positive power, and asserts diameter at most three. The settling
statement is literally `result : ¬ claim`.

## Motivation

The diameter bound would sharply restrict the geometry of graphs whose every
positive power is well-covered. A Cartesian clique factor preserves all-power
well-coveredness when enough labels are available, while increasing diameter.

## Gap

The source v1 explicitly asks the question. The supplied literature reading
reports only v1 and no follow-up found; this is `not-found-in-searched-scope`.
A local search of D5, Problems and Library for the source identifier and
well-covered powers found no prior record. The source and quantified clauses
were supplied with preregistration #14712; no online reading was performed.

## Route

Let H = G □ K_t, where G is finite and connected and t > |V(G)|. Its distance
is d_H((u,a),(v,b)) = d_G(u,v) + 1_{a≠b}. Each independent set of H^d contains
at most one vertex over each base vertex. Its projection has all pairwise
base distances at least d; at distance exactly d the labels must differ.

If the projection of a maximal independent set could be extended by w,
choose a label not used by its at most |V(G)| existing vertices. This extends
the original independent set, a contradiction. Thus for d = 1 its projection
is all of V(G), and for d ≥ 2 it is maximal independent in G^(d−1).
Projection preserves cardinality. Equal cardinalities on the base therefore
give equal cardinalities in every positive power of H. For t ≥ 2 the diameter
increases by one.

The cycle C₇ has diameter three and maximal independent set sizes 3, 2, 1
in its first three powers; all subsequent powers are complete. With t = 8,
the product C₇ □ K₈ is a connected 56-vertex graph of diameter four whose
every positive power is well-covered. The uniform cardinality bound is used;
the smaller C₇ □ K₃ is a separately computed 21-vertex example. Iterating
with t = |V(G)| + 1 supplies every diameter D ≥ 3.

## Falsifier

The construction would fail if projection were not injective, the unused
label did not exist, projection maximality failed, cycle powers had unequal
maximal independent cardinalities, or the product distance formula failed.
The Lean proof discharges these obligations rather than assuming the product
preservation statement.

## Evidence

`D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.result` is the
closed negation of the source diameter assertion. The general product
argument uses Mathlib Cartesian products and graph distances; only the
small base cycle is checked by finite kernel computation. Compilation,
axiom closure and resource measurements are given in REPORT-wcp.md.

## Triage

`theorem`. The proposed universal diameter bound is refuted.

### What the settlement shows

- [proved] C₇ □ K₈ has every positive power well-covered and diameter four.
- [proved] Every natural diameter D ≥ 3 occurs: start with C₇ and repeatedly
  take the Cartesian product with a clique of order one more than the
  current number of vertices.
- [computed: NetworkX, Cartesian products, all-pairs shortest paths, maximal
  cliques of the complement of each power] C₇ □ K₃ has 21 vertices and
  diameter four; the cardinalities of maximal independent sets in successive
  powers are 7, 3, 2, 1, with counts 126, 84, 42, 21 respectively.
- [computed: supplied nauty geng exhaustive result, not rerun here] There
  is no WCP graph of diameter at least four on at most 11 vertices.
- [computed: the same NetworkX procedure] C₇ □ K₂ fails well-coveredness:
  its first power has maximal independent sizes 4 and 6 (14 each), and its
  square has sizes 2 and 3 (14 each). For C₉ □ K₁₀ the square has sizes 3
  and 4, with counts 3000 and 65610; the label construction does not repair
  a base cycle whose square is not well-covered.
- [computed: the same NetworkX procedure] The pentagonal prism C₅ □ K₂
  is WCP, with diameter three and maximal independent sizes 4, 2, 1.
  Its products with K₄, K₅ and K₆ have diameter four and sizes 10, 4, 2, 1
  in successive powers. These finite computations do not prove preservation
  under clique factors smaller than the general sufficient bound.
- [derived: Proposition 3.6 of the source with Example 3.8] The second
  clause of Question 3.9, read literally, is already answered negatively by
  the source paper: the uniform independence blow-ups C₇[rK₁,…,rK₁], r ≥ 2,
  are WCP of diameter three, have no true twins (only false twins) and have
  unbounded order. The d = 1 paragraph of Proposition 3.6 needs a repair: a
  maximal independent set of the blow-up contains every occupied fibre
  completely, so the projected cardinality is multiplied by r; the
  conclusion is unchanged.
- [computed: nauty geng exhaustive search and NetworkX] C₅ □ K_t is WCP of
  diameter three for t = 2, …, 12 and has neither true nor false twins, so
  the second clause also has a negative answer when all twins are excluded;
  WCP twin-free graphs of diameter three number 1, 0, 3, 6, 142 on 7, 8, 9,
  10, 11 vertices. A proof for every t follows from the product theorem
  for t > 5 together with a closed-neighbourhood comparison; it is not
  formalized here.
- [literature] For d = 1 the product theorem is the observation of
  Hartnell, Rall and Wash (On well-covered Cartesian products, Graphs and
  Combinatorics 34 (2018), arXiv:1703.08716, Section 2) that K_t □ F is
  well-covered when t > Δ(F). Brown and Hoshino (Well-covered circulant
  graphs, Discrete Mathematics 311 (2011), Theorem 4.1) classify the
  well-covered powers of cycles, C_n^d well-covered iff n ≤ 3d + 2 or
  n = 4d + 3, which gives the seeds C₅ and C₇.
- [open] The smallest order of a WCP graph of diameter four is between
  12 and 21, conditional on the supplied exhaustive lower-bound computation.

## ASSUMED-UNVERIFIED

The literature reading and nauty exhaustive search are attributed to the
supplied source material; neither was independently rerun here. No-network
execution precludes checking later versions or priority. The 12-vertex lower
bound relies on that exhaustive-search evidence. Kernel compilation of the
formal construction is separate from these evidence boundaries.
