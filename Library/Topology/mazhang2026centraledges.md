---
bibkey: mazhang2026centraledges
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)"
doi: "10.5281/zenodo.24369118"
url: "https://doi.org/10.5281/zenodo.24369118"
claim: "Lemma 2: a finite metric space with n points and k central distances (zero included) has at least (k-1)⌈n/2⌉ central edges; Theorem 4: three-central n-point ultrametrics have at least 2n-4+⌈n/2⌉ central edges, sharply."
strata_touched:
  - D5/S3/Combinatorics/Geometry/CentralEdgeCover
  - D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum
  - D5/S3/Combinatorics/Geometry/ThreeCentralMinimum
  - D5/S3/Combinatorics/Geometry/CompleteCentralParity
  - D5/S3/Combinatorics/Geometry/MinimumCentralOrder
  - D5/S3/Combinatorics/Geometry/CentralSizeEdgeMinima
  - D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum
  - D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric
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

Equation (1) (Section 2): if F_1, ..., F_s are edge-disjoint spanning edge covers of K_n, n >= 3,
every edge of F_i gets the length a_i with the a_i distinct in [1, 2), and every remaining edge
gets its own distinct length in [1, 2) different from all a_i, then this is a metric with
C(X) = {0, a_1, ..., a_s} and central edge set F_1 ∪ ... ∪ F_s. In a triangle the longest side
is less than 2 while the other two sum to at least 2; each a_i is central; each remaining length
occurs on one edge and misses a third vertex. EdgeCoverLengthMetric.result formalizes it for any
closed band [c, 2c] with c > 0 (the source's band is [1, 2), contained in c = 1) and without
requiring the a_i to be distinct.

Theorem 3 (Section 2): for every n >= 4 the minimum number of central edges among
three-central n-point metric spaces is 2⌈n/2⌉; the lower bound is Lemma 2 with k = 3. The
attaining space takes two disjoint covering pair classes (even- and odd-indexed cycle edges,
with the chord {0,2} for odd n) at distinct class lengths a_i in [1,2) and all other distances
distinct in [1,2), following the narrow-band realization of O. Dovgoshey and O. Rovenska
(Theorem 3.8, formula (19)).

Theorem 4 (Section 3): for n >= 4 the least number of central edges of a three-central
n-point ultrametric is 2n-4+⌈n/2⌉, with equality exactly when the diametrical graph is complete
bipartite with parts of sizes 2 and n-2 and the other positive central distance has ⌈n/2⌉ edges.
The diameter classes are fully joined at the diameter, and merging classes reduces to two parts
with p(n-p) - 2(n-2) = (p-2)(n-p-2) >= 0; a nested pair/triple ultrametric attains the bound.

Theorem 5 (Section 4): for n >= 1 a metric space of order n with complete n-central graph
exists if and only if n = 1 or n is even. The source shows that each positive central distance
then occurs exactly once in every row, so its edges form a perfect matching and n is even;
equivalently, for odd n >= 3 Lemma 2 would require more than n(n-1)/2 edges. For even n a
one-factorization of K_n (Harary) with one distance per factor realizes it. The realization
step, constant lengths in [1,3/2) on chosen spanning covers and distinct lengths elsewhere,
uses the narrow-band principle of Dovgoshey and Rovenska (proof of Theorem 3.8, formula (19)).

Corollary 6 (Section 4): for k >= 1 the least order v(k) of a metric space with |C(X)| = k is
1 for k = 1, k for even k, and k+1 for odd k >= 3. This answers Problem 4.3 of Dovgoshey and
Rovenska. The source uses the row bound k <= |X| (the center lies in the distances from one
point) and Theorem 5; equivalently, Lemma 2 against the n(n-1)/2 pairs gives k <= n, and
k <= n-1 for odd n >= 3. A one-factorization of K_(k+1) or K_k with k-1 factors at constant lengths in [1,3/2) and the
remaining edges at distinct lengths in (3/2,2) attains the bound.

Corollary 7 (Section 5): for n >= 3 the feasible center sizes are 1 <= k <= n for even n and
1 <= k <= n-1 for odd n; n = 1 allows only k = 1 and n = 2 only k = 2. Each feasible pair
attains (k-1)⌈n/2⌉ central edges. The source bounds k by the row bound and Theorem 5 and the
edges by Lemma 2. For odd n the n near-one-factors of K_n are completed by
orienting the path formed by two reserved factors, which gives n-2 disjoint spanning edge
covers of size (n+1)/2; the source credits Andersen's cover-index criterion as antecedent.

Corollary 8 (Section 5): for n >= 2 a nonempty central graph has at least ⌈n/2⌉ edges; the
equality graphs are (n/2)P2 for even n and P3 ∪ ((n-3)/2)P2 for odd n, and they are bicentral;
without nonemptiness the minimum is zero for n >= 3. The nonempty minimum is Dovgoshey and
Rovenska's Theorem 3.10; the source corrects the odd component count printed in their Theorem
3.12 (P3 ∪ hP2 for n = 2h+1 has n+2 vertices).
