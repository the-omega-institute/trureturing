# The native constant-one unit

## Abstract

The native constant-one unit

**Definition 1.1 (The native constant-one unit).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.balancedUnitSeries`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.balancedUnitSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For S=s/z and T=z/x in the native cumulative chart, the unit is (1+ST)^a0 (1+ST-T)^k (1-T)^k. Only native power series are substituted.

**Definition 1.2 (Signed native coefficients).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.rawBalancedCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.rawBalancedCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse unit times the reordered native numerator is read at (s+k,s+z+k+a2,s+z+x+a0+a1+a2+3k), with zero extension at every negative native coordinate.

**Theorem 1.3 (Exact literal clearing action).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.raw_balanced_action`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.raw_balanced_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite monomial translations and native unit cancellation recover the original signed numerator under the literal balanced polynomial for every signed target and every generally infinite numerator.

**Theorem 1.4 (Support of the inverse).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.raw_balanced_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.raw_balanced_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse expression has the uniform s cutoff -k and, at each fixed s, the z cutoff -(s+k+a2). No x bound is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.balancedUnitSeries`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.rawBalancedCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.raw_balanced_action`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedNativeInverse.raw_balanced_support`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial](ThreeFieldBalancedPolynomial.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentAction](ThreeFieldFinalLaurentAction.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse](ThreeFieldInnerNativeInverse.md)
