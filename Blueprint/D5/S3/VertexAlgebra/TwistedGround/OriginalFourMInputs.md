# OriginalFourMInputs

## Abstract

Original lattice twisted-sector coefficient reduction, preserving the original carriers and operators.

**Theorem 1.1 (Compatible original polynomial tensors).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.tensor_input_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.tensor_input_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An original polynomial P has sigma P=-P and signed odd weighted degree 2H-3. Every selected ActualGround vector x gives tensorInput with underlying vector P tensor x in the original paritySpace(-1). Its actualTensorL0 eigenvalue is H. The proof uses the original zero-mode theorem, whose constant shift is rank/16; rank 24 makes the oscillator half-energy H-3/2. Zero polynomials and zero ground vectors remain allowed.

**Theorem 1.2 (Finite expansion of all three inputs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex trilinear map on the original negative-parity tensor module and every original u,v,w, expand each input using MixedJacobiFinite.actual_input_basis_expansion through legal OpenPrivate. The three sums run over the attached actual finite coordinate supports, with the product of their actual basis coefficients. Finite map and scalar distribution commute these sums.

**Theorem 1.3 (Homogeneous tensors suffice for an all-input trilinear law).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_ext`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual_input_basis_energy theorem and negative_support identify every term of the preceding expansion with a compatible homogeneous polynomial tensor. Thus zero on all these original tensors implies zero on every original input. This neither changes the carrier to a chosen basis nor assumes extension from the vacuum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_ext`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.tensor_input_energy`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite](MixedJacobiFinite.md)
