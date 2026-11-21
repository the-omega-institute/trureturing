---
bibkey: mazhang2026centraledgesv4
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Refuting Dovgoshey–Rovenska's central-edge conjectures: sharp bounds and tree corollaries"
doi: "10.5281/zenodo.24389010"
url: "https://doi.org/10.5281/zenodo.24389010"
claim: "Theorem 5: for every n ≥ 8 the minimum number of central edges among n-point ultrametric spaces with |C(X)| = 4 is 6n-16-4⌊n/4⌋+⌈n/2⌉, and no such space exists for n < 8."
strata_touched:
  - D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Topology/mazhang2026centraledgesv4 -->
# Four-element ultrametric centers

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, version 4, exact-version DOI
https://doi.org/10.5281/zenodo.24389010, Theorem 5 and Equation (3), Section 4 ("Four-element
ultrametric centers"). The central-edge question is posed by O. Dovgoshey and O. Rovenska
(arXiv:2610.11596, Section 4); version 3 of the same note (DOI 10.5281/zenodo.24369118) is
recorded in mazhang2026centraledges.

## Statement

For a finite metric space X let C(X) be the set of t >= 0 such that every point has a point,
itself when t = 0, at distance t; central edges join distinct points at a central distance.
Theorem 5: for every n >= 8 the minimum number of central edges among n-point ultrametric
spaces with |C(X)| = 4 is 6n-16-4⌊n/4⌋+⌈n/2⌉, and no such space exists for n < 8.

The proof writes C(X) = {0, a, b, D} with D the diameter. The closed balls of radius b number at
most ⌊n/4⌋, since each splits into at least two classes of distance below b with at least two
points each; class merging gives at least 2s-4 edges of length b in a ball of s points. The
length a has at least ⌈n/2⌉ edges, and the diameter classes contribute at least 4(n-4) edges.
A nested construction with noncentral intermediate distances attains every bound.
