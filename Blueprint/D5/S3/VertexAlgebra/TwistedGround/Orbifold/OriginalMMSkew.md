# Signed Skew Symmetry of the Original Two-Twisted Coefficients

## Abstract

Signed Skew Symmetry of the Original Two-Twisted Coefficients

**Theorem 1.1 (Signed skew symmetry on all negative twisted states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew.originalI_skew`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew.originalI_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be rank-24 lattice data with unit Gram determinant and positive-definite real Gram form. For every integer mode n and every pair u, v in the original negative twisted sector, originalI at mode n on u and v equals the algebraic sum over natural j of the j-th power of fixed translation applied to originalI at mode n + j on v and u, scaled by the sign (−1) to the power n + j + 1 divided by j!. The equality holds in the original fixed carrier, and the sum has finite support by mode truncation.

For homogeneous inputs of weights H and K, the target grade is d = H + K − n − 1. Pairing against that grade turns translation into lowering on the test vector. The corrected-field adjoint gives a third finite index, which moves outside the two twisted lowering ranges after the phases and modes are aligned. The grade pairing recovers equality of the coefficients, and bilinearity extends it over the finite parity basis expansions of both inputs.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew.originalI_skew`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints](OriginalSkewAdjoints.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients](../OriginalFourMCoefficients.md)
