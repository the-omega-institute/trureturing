# Affine Lines over a Finite Field

## Abstract

The elementary affine plane over a finite field has `card F + 1` lines through
each point, and every two distinct points determine exactly one line.

**Theorem 1.1 (Lines through a point).** For a finite field `F` and
`p : F × F`,

\[
\#\{\ell : \text{AffineLine}(F) \mid p \in \ell\}=|F|+1.
\]

**Theorem 1.2 (Unique line through two points).** If `p ≠ q`, there is a
unique affine line containing both `p` and `q`.

Both statements are machine-checked in Lean as
`card_affineLines_through` and
`exists_unique_line_through_distinct_points` in
`D5/S3/Geometry/FiniteGeometry/AffinePlaneLines`.

## Construction and proof

The lines are graphs `y = m x + b` and vertical lines `x = c`. For a fixed
point `p`, each slope `m` gives the graph with intercept `p.2 - m * p.1`,
and the one vertical line through `p` gives an `Option F` parametrization.
The inverse reads the slope of a graph and sends a vertical line to `none`.

For two points with equal first coordinates, distinctness forces distinct second
coordinates, so only the common vertical line can contain both. With unequal
first coordinates, subtraction and division give the unique slope
`(q.2 - p.2) / (q.1 - p.1)`, and then the intercept is forced by either point.

## Scope

This file formalizes the affine coordinate model over a field. It does not
develop projective completion, parallel classes, or incidence axioms beyond the
two stated consequences.

## References

- Dembowski, *Finite Geometries*, Springer, 1968, Chapter I.
- Hirschfeld, *Projective Geometries over Finite Fields*, 2nd ed., §1.1.
- Truth anchors: `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.card_affineLines_through`,
  `D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.exists_unique_line_through_distinct_points`.
