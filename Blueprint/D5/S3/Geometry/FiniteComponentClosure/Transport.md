# Transport

## Abstract

Actual continuous maps and inverse homotopies for joins, cone-base suspension homeomorphisms, Euclidean sphere models, and finite coordinate coproducts.

Actual continuous maps and inverse homotopies for joins, cone-base suspension homeomorphisms, Euclidean sphere models, and finite coordinate coproducts.

**Definition 1.1 (Native finite sphere models).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Transport.sphereComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Transport.sphereComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-dimensional sphere is the complex of two distinct vertices. Higher sphere complexes are iterated simplicial joins with this two-point complex. Ghost ambient vertices are permitted; no unproved singleton face is added.

**Definition 1.2 (Actual Euclidean spheres).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Transport.sphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Transport.sphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural dimension d, the coordinate realization of sphereComplex d is homeomorphic to the standard unit sphere in Euclidean space of dimension d+1. The base case is the explicit two-point homeomorphism; the induction uses the actual simplicial-join realization homeomorphism and the existing Euclidean sphere-join homeomorphism.

## References

- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Transport.sphereComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Transport.sphereHomeomorph`
- Dependency: [D5/S3/Geometry/EuclideanSphereJoin](../EuclideanSphereJoin.md)
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](../FiniteConeUnionWedge.md)
- Dependency: [D5/S3/Geometry/FiniteVertexCylinder](../FiniteVertexCylinder.md)
- Dependency: [D5/S3/Geometry/SingletonRetractionBasedInverse](../SingletonRetractionBasedInverse.md)
