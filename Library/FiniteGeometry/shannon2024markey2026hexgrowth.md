---
bibkey: shannon2024markey2026hexgrowth
authors: Scott R. Shannon; Aidan Markey
year: 2024
title: "OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth"
doi: null
url: https://oeis.org/A374338
claim: "A374338 conjectures the three vertex-count formulas; A400701 conjectures a(n) = A374338(n) + 4*n + 7 for n > 1."
strata_touched:
  - D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth
  - D5/S3/Geometry/ShannonFixedRadiusCircleVertices
  - D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A374338

Related source: https://oeis.org/A400701

The source records are OEIS A374338 revision 15 (2024) and A400701 revision 30 (2026).
The year field records the earlier source; the two records have separate authors.
There is no paper page number, DOI or arXiv identifier.

## Source statements

A374338 NAME, verbatim:

> Start with two vertices and draw a circle around each whose radius is the distance between the vertices. The sequence gives the number of vertices constructed after n iterations of drawing circles with this same radius around every new vertex created from all circles' intersections. See the Comments.

A374338 COMMENTS, verbatim:

> Start with two vertices and, using each as the center, draw a circle around each whose radius is the distance between the vertices. These circles' intersections create two additional vertices, so after the first iteration four vertices exist. Using these four vertices as centers draw four new circles whose radius is the same as the distance between the initial two vertices. These circles' intersections create eight new vertices. Repeat this process n times; the sequence gives the number of vertices after n iterations.

A374338 FORMULA, verbatim:

> Conjectured:
> If n = 3*k + 1, k >= 0, a(n) = (3*n^2 + 5*n + 4)/3.
> If n = 3*k, k >= 1, a(n) = (3*n^2 + 5*n)/3.
> If n = 3*k - 1, k >= 1, a(n) = (3*n^2 + 5*n + 2)/3.

The iteration-2 illustration, https://oeis.org/A374338/a374338_1.jpg,
states “Total vertices = 8.” Counts include retained vertices; the radius
remains the distance between the two distinct initial Euclidean points.
The natural-number divisions in the formal statements are integer division.

A400701 NAME, verbatim:

> Start with a set of five adjacent collinear points in a hexagonal lattice. Every iteration, add to the set the points in the lattice which are adjacent to at least two points already in the set. This sequence gives the number of points in the set after n iterations.

A400701 FORMULA, verbatim:

> Conjectured: For n > 1: a(n) = A374338(n) + 4*n + 7.

The lattice has six unit neighbors at each site. Finite windows have a spare
layer around the region reachable in the selected number of iterations;
no wraparound edge is present.

## Evidence and limits

The finite checker is in the-omega-institute/trureturing-experiments at commit
604fd09490d8ed3d1f66d03c2ac5c06b033c81c3,
path docs/reports/a400701-hexgrowth/check.py, SHA256
7751e963e186b3c64fa80307e6324d3a3bfb6603d72c4cb6e210c58254fe0995.
Its recorded exit code is 0 and its final line is ALL_CHECKS_OK.
These are finite experiment readings, separate from the unbounded proofs.

Issue https://github.com/the-omega-institute/trureturing/issues/21460 gives
the source and literature screen; the related conjecture is issue
https://github.com/the-omega-institute/trureturing/issues/21459.
Literature completeness is ASSUMED-UNVERIFIED. Region counts, edge counts,
arbitrary seed lengths and generating functions remain outside these claims.
