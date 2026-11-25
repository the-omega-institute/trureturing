# The sphere wedge of the signed fair-bias complex

## Abstract

Collapsing the retained realization exhibits the homotopy type of the signed complex.

**Theorem 1.1 (The core projection and the based sphere wedge).**

Lean statement: `D5/S3/TotalVariation/FairBiasSphericalWedge.exists_spherical_wedge`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasSphericalWedge.exists_spherical_wedge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the signed fair-bias complex has a nonempty facet. The retained subcomplex collapses to the first facet's simplex and is contractible. The quotient map that collapses the retained realization is a homotopy equivalence.

The quotient is homeomorphic to the wedge of one standard sphere for each facet equal to its restriction face. Each sphere has dimension equal to the number of labels minus the column rank minus one. The homeomorphism sends the collapsed class to the wedge basepoint.

On each simplex, collapsing the entire boundary gives a sphere. In the singleton case the boundary is empty, and the simplex point and the added basepoint form a zero-sphere. The factor maps identify points on each boundary and identify all the boundary classes with the common basepoint. These are exactly the identifications of the attachment quotient. On each original coordinate simplex, the homeomorphism agrees with its sphere map followed by inclusion of the corresponding wedge factor. The image of the simplex together with the common basepoint covers that factor. If there are no such facets, the quotient is a point.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasSphericalWedge.exists_spherical_wedge`
- Dependency: [D5/S3/Geometry/CompactWedgeFiniteFactor](../Geometry/CompactWedgeFiniteFactor.md)
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/BasedJoin](../Geometry/FiniteComponentClosure/BasedJoin.md)
- Dependency: [D5/S3/Geometry/FiniteSimplexBoundarySphere](../Geometry/FiniteSimplexBoundarySphere.md)
- Dependency: [D5/S3/TotalVariation/FairBiasFacetQuotient](FairBiasFacetQuotient.md)
