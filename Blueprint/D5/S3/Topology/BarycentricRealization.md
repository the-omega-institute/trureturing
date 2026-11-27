# Realization of finite barycentric subdivisions

## Abstract

Realization of finite barycentric subdivisions

**Theorem 1.1 (The realization homeomorphism).**

Lean statement: `D5/S3/Topology/BarycentricRealization.realizationHomeomorph`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BarycentricRealization.realizationHomeomorph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Replacing each vertex of an ordinary subdivision by the barycentre of its old face induces a homeomorphism of the two finite coordinate realizations.

The greatest face of a positive flag is recovered as the old support. Its coefficient is determined by the least positive coordinate. Subtracting that contribution and repeating gives existence and uniqueness of the flag coordinates. The same support statement identifies the homeomorphism on every subcomplex.

## References

- Truth anchor: `D5/S3/Topology/BarycentricRealization.realizationHomeomorph`
- Dependency: [D5/S3/Geometry/FiniteSimplicialJoin](../Geometry/FiniteSimplicialJoin.md)
- Dependency: [D5/S3/Geometry/FiniteSimplicialOpenCover](../Geometry/FiniteSimplicialOpenCover.md)
- Dependency: [D5/S3/Geometry/FiniteSubcomplexCylinder](../Geometry/FiniteSubcomplexCylinder.md)
- Dependency: [D5/S3/Topology/BarycentricBaseRigidity](BarycentricBaseRigidity.md)
