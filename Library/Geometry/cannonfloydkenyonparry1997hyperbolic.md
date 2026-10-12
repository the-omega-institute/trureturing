---
bibkey: cannonfloydkenyonparry1997hyperbolic
authors: James W. Cannon, William J. Floyd, Richard Kenyon, and Walter R. Parry
year: 1997
title: Hyperbolic Geometry
doi: null
url: https://library.slmath.org/books/Book31/files/cannon.pdf
claim: Classical uniqueness and projective descriptions of hyperbolic geodesics, upper-sheet preservation for Lorentz isometries, and the Lorentz inner-product distance identity.
strata_touched:
  - D5/S3/Geometry/Hyperideal/LengthGramMetricSegments
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Geometry/cannonfloydkenyonparry1997hyperbolic -->
# Classical hyperbolic geodesics and Lorentz distance

## Source and scope

The source is the chapter in *Flavors of Geometry*, MSRI Publications,
volume 31. Theorem 9.3 on printed pages 78-79 classifies upper-half-space
geodesics and proves uniqueness of the geodesic joining two points.
The discussion on page 80 identifies Klein geodesics as straight line
segments and hyperboloid geodesics as intersections with two-dimensional
vector subspaces under central projection.

Section 10, Theorem 10.1 on page 82 separates preservation of the Lorentz
inner product from preservation of the upper sheet: its second condition
requires the last entry of the last matrix column to be positive.
The lemma on page 83 gives the identity a * b = -cosh(d(a,b)) for points
on the upper unit hyperboloid, with space-positive, time-negative signature.

## Repository application boundary

These are classical ingredients of the metric-segment construction.
The exact application to the repository's frozen cutBody and radial
definitions, using the same supplied matrix m and map f and identifying
both the original coefficient-segment image and the ambient between-set,
is a repository derivation. This custom theorem is not stated verbatim
in the cited chapter. The acknowledgement makes no novelty claim.

## Verified locator

- Primary PDF: https://library.slmath.org/books/Book31/files/cannon.pdf
- Verified passages: Theorem 9.3, printed pages 78-79; projective model
  discussion, page 80; Section 10, Theorem 10.1, page 82; distance lemma,
  page 83.
- The PDF title page identifies the authors, title, volume 31, and year 1997.

## Supporting-plane application

The full plane realization uses the same classical Lorentz-isometry and
distance ingredients (Section 10, Theorem 10.1, page 82, and the distance
lemma on page 83). Its auxiliary reflection is required to preserve the
future sheet, not just the bilinear form. Together with the existing H2
metric formula, the repository construction parametrizes the entire
original spacelike supporting plane in its existing H3 metric. It does
not change the chosen length Gram frame or its radial body. This precise
Lean-type transport is a repository derivation, with no novelty claim.
It does not establish the full tetrahedron realization or its angles.
