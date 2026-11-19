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
Rovenska. A space has at most n central values; at equality the central graph is complete, so
Theorem 5 excludes odd n >= 3, and capping the round-robin distances attains every bound.
