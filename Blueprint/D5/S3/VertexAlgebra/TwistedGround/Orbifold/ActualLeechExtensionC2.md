# The C2 Quotient Comparison for the Actual Extension

## Abstract

The product of the fixed and relative twisted quotients surjects onto the actual extension quotient.

The inputs are lattice data D, a proof that det(D.G) is a unit, and a proof that the Gram matrix is positive definite over the reals. The carrier of the assembled field is the product of the fixed lattice sector and the negative twisted parity sector.

**Definition 1.1 (The relative twisted subspace).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.relativeOddC2`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.relativeOddC2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the complex span of the minus-two coefficients of the actual fixed-source field acting on negative twisted states.

**Definition 1.2 (The extension C2 subspace).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.extensionC2`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.extensionC2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the complex span of the minus-two products of arbitrary pairs of states of the assembled carrier.

**Definition 1.3 (The comparison map).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two sector inclusions followed by the extension quotient map kill the respective C2 subspaces. The descended linear maps give a map from the product of the fixed quotient and relative twisted quotient.

**Theorem 1.4 (The comparison on representatives).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair of quotient classes maps to the extension quotient class of the corresponding paired state.

**Theorem 1.5 (Surjectivity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a representative of an arbitrary extension quotient class. The quotient classes of its two coordinates map to the original class.

**Theorem 1.6 (Surjectivity for the Leech extension).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.leechQuotientComparison_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.leechQuotientComparison_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the comparison to the chosen positive-definite unimodular Leech lattice.

**Theorem 1.7 (Finite dimensionality from the relative quotient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.leech_extension_c2_cofinite_of_relative_odd_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.leech_extension_c2_cofinite_of_relative_odd_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the chosen Leech data, the comparison uses the fixed-sector theorem leech_fixed_c2_cofinite. Given finite dimensionality of the negative twisted relative quotient over the complex numbers, finite dimensionality of the full extension quotient follows.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.extensionC2`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.leechQuotientComparison_surjective`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.leech_extension_c2_cofinite_of_relative_odd_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison_mk`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.quotientComparison_surjective`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.relativeOddC2`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Cofinite](../../Lattice/FixedC2/ActualFixedC2Cofinite.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField](OriginalOrbifoldField.md)
