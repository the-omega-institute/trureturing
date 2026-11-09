# Multiplication on original critical BRST cohomology

## Abstract

Multiplication on original critical BRST cohomology

The carrier is the actual kernel of the original tensor totalCharge modulo its actual image. Rank 26 and both inverse Gram identities remain explicit. The existing b(-1) Ward identity makes the original translation exact on cycles, so translation vanishes on the quotient and covariance kills every mode except -1. Multiplication is the descended bilinear -1 mode. The original supported tensor iterate proves associativity for arbitrary classes. Signed locality gives supercommutativity for homogeneous classes; spectral projections express braiding for arbitrary parity mixtures. Nonzero classes, closure, associativity and locality are not premises.

The original lattice, ghost, Scott Carnahan vertexAlg, Kalle Kytola Sugawara and Mathlib attribution remains in the imported sources. Native compilation, measured axiom closure, semantic registration and formal publication are distinct checks. No literature novelty or completion of string theory or AdS/CFT is claimed.

**Theorem 1.1 (Exact translation vanishes in cohomology).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.translation_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.translation_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original b(-1) operator supplies the boundary witness for every translated cycle.

**Theorem 1.2 (All modes except -1 vanish).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.mode_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.mode_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation covariance and the nonzero scalar -(k+1) handle every integer k other than -1.

**Theorem 1.3 (Associativity of the actual -1 product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_assoc`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite action supports are carried through the cycle subtype and quotient before reducing the original iterate sums.

**Theorem 1.4 (Homogeneous supercommutativity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_supercomm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_supercomm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact eigenvalue hypotheses on the two classes determine the Koszul sign; homogeneous cycle lifts are proved in the field supplier.

**Theorem 1.5 (Braiding for arbitrary mixed classes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_mixed_braiding`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_mixed_braiding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four even and odd terms retain the actual quotient parity projections.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.mode_eq_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_assoc`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_mixed_braiding`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_supercomm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.translation_eq_zero`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyLaws](LatticeBRSTCohomologyLaws.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateFieldIterate](LatticeMatterGhostStateFieldIterate.md)
