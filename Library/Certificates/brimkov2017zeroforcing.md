---
bibkey: brimkov2017zeroforcing
authors: Boris Brimkov
year: 2017
title: "Graph Coloring, Zero Forcing, and Related Problems"
doi: null
url: "https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content"
claim: "Proposition 7.7: if n >= 2, the connected forcing polynomial of the path is Z_c(P_n; x) = 2x + sum_(i=2)^n (n - i + 1) x^i."
strata_touched:
  - D5/S3/Combinatorics/Graph/ZeroForcing/PathConnectedForcing
license: citation-only
triage: anchor
---

# Connected forcing polynomial of the path

## Verified locator

PhD thesis, Rice University, May 2017, Chapter 7, Proposition 7.7, printed pages 165–166. Source
PDF: https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content .

## Source statement

> Definition 7.1. Let G be a graph. Let z(G; i) and z_c(G; i) respectively be the number of zero
> forcing sets and the number of connected forcing sets of G with cardinality i. The zero forcing
> polynomial of G is defined as Z(G; x) = Σ_{i=Z(G)}^n z(G; i) x^i. The connected forcing
> polynomial of G is defined as Z_c(G; x) = Σ_{i=Z_c(G)}^n z_c(G; i) x^i.

> Proposition 7.7. If n ≥ 2, Z_c(P_n; x) = 2x + Σ_{i=2}^n (n − i + 1) x^i.

The source's proof: either end vertex is a connected forcing set of size 1; for 2 ≤ i ≤ n a
connected forcing set of size i is determined by its vertex of smallest label in a depth-first
order from an end, which leaves n − i + 1 choices.

## Mathematical scope

PathConnectedForcing.result states the coefficients of Z_c(P_n; x) for Mathlib's pathGraph n and
the connected forcing sets of ConnectedForcingCrossingRefutation (zero forcing sets inducing a
connected subgraph): z_c(P_n; 0) = 0, z_c(P_n; 1) = 2, and z_c(P_n; i) = n + 1 − i for every
i ≥ 2, which is 0 for i > n. PathConnectedForcing.connected_forcing_iff characterizes the
connected forcing sets of P_n, n ≥ 2: the intervals with at least two vertices and the two end
vertices. An interior vertex alone forces nothing, which the source's count uses implicitly.
