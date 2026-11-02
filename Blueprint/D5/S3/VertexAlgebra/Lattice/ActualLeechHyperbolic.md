# The actual Leech lattice and the original hyperbolic plane

## Abstract

The actual Leech lattice and the original hyperbolic plane

One accepted RealLeech existential supplies both D and its integral coordinate equivalence e. Both are reused throughout. The geometric product is the actual RealLeech lattice times two integer axes in RealLeech.Space times R times R, with dot/8 on the Leech factor and the original hyperbolic cross-pairing. The inclusion range is exactly this product submodule. Testing the dual against Leech vectors and each integral axis proves geometric selfduality; the actual even Leech norm proves evenness of the product. Every original charge has the actual product pairing. Rank 26, determinant -1, signature (25,1), arbitrarily negative energies, the critical BRST square and the charge-adapted positive transverse frame are applications of these constructions and existing suppliers. This is the Leech dependency for the fake Monster construction. True V-natural, cohomological positivity, full Monster moonshine, string theory and AdS/CFT remain separate mathematical objectives.

**Definition 1.1 (All original charge coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.coordinates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full original charge group is integrally linearly equivalent to the actual RealLeech lattice times two integer axes, using the same accepted Leech witness.

**Definition 1.2 (The actual geometric product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.productLattice`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.productLattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This submodule is the actual RealLeech image times the two integer axes in the real ambient product. It is proved discrete and spanning.

**Theorem 1.3 (The exact actual inclusion range).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.productLattice_eq_range`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.productLattice_eq_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual ambient inclusion has range exactly the product lattice; both integral axes are unrestricted.

**Theorem 1.4 (Geometric selfduality).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.product_self_dual`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.product_self_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dual membership is tested against actual Leech vectors and each integral axis. The reverse inclusion uses the actual Leech integral pairing and the hyperbolic cross terms.

**Theorem 1.5 (Geometric evenness).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.product_even`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.product_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Leech even norm plus twice the product of the two integer coordinates gives an even product norm, including all negative norms.

**Theorem 1.6 (The original all-charge pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.actual_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.actual_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of original charges, the original extended integral pairing equals the actual geometric product pairing after the same coordinate equivalence and ambient inclusion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.actual_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.productLattice`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.productLattice_eq_range`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.product_even`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic.product_self_dual`
- Dependency: [D5/S3/Arith/Lattices/Golay/RealLeech](../../Arith/Lattices/Golay/RealLeech.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension](OrderedHyperbolicExtension.md)
