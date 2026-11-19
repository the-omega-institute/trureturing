---
bibkey: mazhang2026centraledges
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)"
doi: "10.5281/zenodo.24369118"
url: "https://doi.org/10.5281/zenodo.24369118"
claim: "Lemma 2: a finite metric space with n points and k central distances (zero included) has at least (k-1)⌈n/2⌉ central edges."
strata_touched:
  - D5/S3/Combinatorics/Geometry/CentralEdgeCover
  - D5/S3/Combinatorics/Geometry/CompleteCentralParity
  - D5/S3/Combinatorics/Geometry/MinimumCentralOrder
  - D5/S3/Combinatorics/Geometry/CentralSizeEdgeMinima
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Topology/mazhang2026centraledges -->
# Central-distance edge-cover lower bound

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, version 3, exact-version DOI
https://doi.org/10.5281/zenodo.24369118, Lemma 2, Section 2. It refines the earlier
nonempty central-graph bound of O. Dovgoshey and O. Rovenska (arXiv:2610.11596).

## Statement

For a nonempty finite metric space (X,d) with n points let C(X) be the set of t >= 0 such that
every point has another point, or itself when t = 0, at distance t. The central graph joins
distinct points whose distance lies in C(X). If |C(X)| = k then the central graph has at least
(k-1)⌈n/2⌉ edges: for each nonzero central value the edges of that length cover every point,
and edges of different lengths are distinct.

Theorem 5 (Section 4): for n >= 1 a metric space of order n with complete n-central graph
exists if and only if n = 1 or n is even. For odd n >= 3 Lemma 2 would require more than
n(n-1)/2 edges; for even n a one-factorization of K_n (Harary) with one distance per factor
realizes it.

Corollary 6 (Section 4): for k >= 1 the least order v(k) of a metric space with |C(X)| = k is
1 for k = 1, k for even k, and k+1 for odd k >= 3. This answers Problem 4.3 of Dovgoshey and
Rovenska. Lemma 2 against the n(n-1)/2 pairs gives k <= n, and k <= n-1 for odd n >= 3; a
one-factorization of K_(k+1) or K_k with k-1 factors at constant lengths in [1,3/2) and the
remaining edges at distinct lengths in (3/2,2) attains the bound.

Corollary 7 (Section 5): for n >= 3 the feasible center sizes are 1 <= k <= n for even n and
1 <= k <= n-1 for odd n; n = 1 allows only k = 1 and n = 2 only k = 2. Each feasible pair
attains (k-1)⌈n/2⌉ central edges. For odd n the n near-one-factors of K_n are completed by
orienting the path formed by two reserved factors, which gives n-2 disjoint spanning edge
covers of size (n+1)/2; the source credits Andersen's cover-index criterion as antecedent.
