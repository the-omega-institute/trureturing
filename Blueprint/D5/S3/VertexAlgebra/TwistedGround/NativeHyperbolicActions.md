# Native Hyperbolic Actions

## Abstract

Hyperbolic coordinates normalize the exact chosen native Leech ground action.

**Theorem 1.1 (Native Hyperbolic Actions).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeHyperbolicActions.coordinate_action_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeHyperbolicActions.coordinate_action_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeGround is literally ActualGround(ExplicitLeechLattice.data,determinantUnit). nativeRho is the original nested Classical.choose representation. Neither is a newly selected existential witness. The chosen rank is twelve and the chosen carrier has complex dimension 4096.

The hyperbolic frame makes every diagonal entry of squareCorrection zero. Consequently the original actionScalar is a real sign, not an arbitrary fourth root. Evaluating the existing reducedRepresentation multiplication law on the constant-one function at zero establishes the scalar multiplication identity. Multiplication of normalized native operators then has exactly the standard binary cocycle.

The left and right coordinate subgroups give commuting involutions within each subgroup. Across the two subgroups their commutation sign is complexSign(dot(right,left)). The functions involutionE and involutionF are these original native endomorphisms at the coordinate units.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeHyperbolicActions.coordinate_action_mul`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/LeechQuadratic](LeechQuadratic.md)
