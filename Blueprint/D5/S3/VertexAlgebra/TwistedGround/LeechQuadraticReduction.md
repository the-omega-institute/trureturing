# The Original Quadratic Refinement

## Abstract

The original cocycle diagonal is the integral half-norm quadratic refinement.

**Theorem 1.1 (The Original Quadratic Refinement).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction.quadratic_integral`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction.quadratic_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original even integral LatticeData, the bilinear lower-triangular cocycle defines a quadratic form over F2 by evaluation on the diagonal. The original cocycle_reduction and integral_cocycle_square identities identify its value on an integral charge with half the original Gram norm modulo two.

The literal Leech hyperbolic certificate uses this identity to certify singular frame vectors in the original charge coordinates. This is a consumed application of the existing reduction identities, not an independent new half-norm theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction.quadratic_integral`
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../LatticeTwistedGroundRealization.md)
