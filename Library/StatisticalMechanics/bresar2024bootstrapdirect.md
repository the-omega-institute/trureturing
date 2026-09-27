---
bibkey: bresar2024bootstrapdirect
authors: Boštjan Brešar, Jaka Hedžet, Rebekah Herrman
year: 2024
title: "Bootstrap percolation and P_3-hull number in direct products of graphs"
doi: 10.7151/dmgt.2603
url: https://arxiv.org/abs/2403.10957v1
claim: "The paper studies r-neighbour bootstrap percolation on direct products of graphs, proves m(G x H, r) <= |V(G)| when the minimum degree of G is at least r and H is connected (Proposition 3), and asks in Problem 5 to determine m(C_n x P_m, 2)."
strata_touched:
  - D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap
license: citation-only
triage: anchor
---

# Brešar, Hedžet and Herrman, bootstrap percolation in direct products

In `r`-neighbour bootstrap percolation an initial set `A_0 ≠ ∅` of infected
vertices grows by

> A_t = A_{t−1} ∪ {v ∈ V(G) : |N(v) ∩ A_{t−1}| ≥ r}

and `m(G, r)` is the least size of a set that eventually infects every vertex.
The direct product `G × H` has vertex set `V(G) × V(H)`, with `(g, h)` and
`(g', h')` adjacent when `g g' ∈ E(G)` and `h h' ∈ E(H)`.

Proposition 3 shows that a `G`-layer percolates in `G × H` when `δ(G) ≥ r` and
`H` is connected, so `m(C_n × P_m, 2) ≤ n`. The concluding section asks:

> Problem 5. Determine m(C_n × P_m, 2).

with the remark that equality appears to hold for small examples and holds for
`m = 2`.

## Verified locator

- DOI: 10.7151/dmgt.2603 (Crossref record retrieved 2026-09-27: Discussiones
  Mathematicae Graph Theory 46(1) (2026), first page 257; authors Brešar,
  Hedžet, Herrman).
- URL: https://arxiv.org/abs/2403.10957v1 (the only version listed by the arXiv
  API on 2026-09-27); source file `percolation_direct_submitted.tex`: the direct
  product (line 114), the update rule (line 122), Proposition 3
  `prp:basic-upper-bound2` (lines 173–176) and Problem 5 `prob:cyclepath` (lines
  1471–1473, the fifth `prob` environment).
