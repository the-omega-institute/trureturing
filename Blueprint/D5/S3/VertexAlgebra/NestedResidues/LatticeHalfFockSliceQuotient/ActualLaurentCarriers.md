# Actual finite homogeneous Laurent carriers

## Abstract

Actual finite homogeneous Laurent carriers

**Theorem 1.1 (Actual finite homogeneous Laurent carriers).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers.actual_finite_laurent_carriers`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers.actual_finite_laurent_carriers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual current and two physical source slices have three independent locality orders. Their weighted common cleared array has finite homogeneous coefficient slices. For every actual input tensor, linear functional, signed lifts and signed total degree, a finite Laurent polynomial represents that slice in every ordered Hahn expansion.

The construction first supplies the actual common array and supported carriers. Homogeneous multiplication by each labelled difference shifts degree by one; division by the homogeneous clearing polynomial then identifies all ordered scalar coefficients. Negative degrees and zero slices are included. The resulting carriers supply the two actual local branches of the arbitrary-cutoff quotient theorem.

Classical local-field provenance is Matsuo–Nagatomo and Bakalov–Kac (math/0402315). The source retains the mathlib Hahn/Laurent and partial-fraction authors and Scott Carnahan/vertexAlg composition attribution under Apache 2.0. The full quotient and its supporting public computations have an unfinished four-slot audit under issue #20510; source reconstruction alone is not declared_validated.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers.actual_finite_laurent_carriers`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/Locality](../../ChargedResidue/Locality.md)
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/NativeDefect](../../GroundRightCurrentTransport/NativeDefect.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator](../../LatticeHalfFockChargedCollision/WeightedLocalCorrelator.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction](../ContextualKernelExtraction.md)
- Dependency: [D5/S3/VertexAlgebra/RationalCollision](../../RationalCollision.md)
