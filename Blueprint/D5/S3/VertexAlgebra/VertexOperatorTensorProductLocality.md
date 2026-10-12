# Signed Tensor Locality

## Abstract

Nested coefficient bounds for scalar-signed tensor locality.

The signed discrepancy is A_p C_q minus s C_q A_p. Polynomial clearing acts by the coefficient shift f(p+1,q)-f(p,q+1). Ordered products have a uniform upper bound on the inner field index, and a separate outer-mode bound for each inner coefficient. Reversed products have the opposite orientation. The actual nested tensor action uses compatible orientations, not an unbounded mixed product. All summation is pointwise on the input vectors.

Independent input-field locality is a legitimate premise. The scalar exchange sign is not silently replaced by an ordinary commutator. For the intended even matter factor its sign is one; the bc factor can have sign minus one. No generic super tensor state-field algebra is asserted without the Koszul crossing rule.

**Theorem 1.1 (The two-index diagonal has finite support).**

Lean statement: `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.convolution_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.convolution_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inner indices form a finite interval from the two uniform inner-field bounds. For each such index the outer indices lie in a second finite interval. A finite union of these intervals controls the nested coefficient sum. Reversal uses the proved coordinate-swap bijection.

**Theorem 1.2 (Clearing shifts transfer through the diagonal convolution).**

Lean statement: `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.convolution_delta_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.convolution_delta_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer bijections reindex each shift. Finite support of both shifted summands justifies subtraction of the finsums. This is an actual coefficient identity, not an interface assuming tensor locality.

**Theorem 1.3 (The product exchange sign and the sum of clearing orders).**

Lean statement: `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.signedLocal_tensor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.signedLocal_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the U fields have scalar-signed locality with sign s and order N, and the V fields have sign t and order M, their tensor fields have sign s times t and order N plus M. Both ordered actions are identified with actual finite nested convolutions. Clearing powers transfer to the two factors, the factor identities are applied, and tensor induction extends the equality to all vectors. The argument works for arbitrary complex scalars; no use of s squared or t squared equal to one is required.

## References

- Truth anchor: `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.convolution_delta_left`
- Truth anchor: `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.convolution_finite`
- Truth anchor: `D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.signedLocal_tensor`
- Dependency: [D5/S3/VertexAlgebra/VertexOperatorTensorProduct](VertexOperatorTensorProduct.md)
