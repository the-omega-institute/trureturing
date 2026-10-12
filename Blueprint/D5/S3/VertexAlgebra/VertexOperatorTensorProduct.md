# Tensor Fields

## Abstract

Actual integer-mode convolution on the full algebraic tensor carrier.

For arbitrary complex modules U and V, the constructor uses the pinned Mathlib VertexOperator type and the actual algebraic tensor product. On u tensor v, normalized mode n is the sum of A_i u tensor B_(n-1-i) v. Its support lies in the integer interval from n-1-upper(B,v) to upper(A,u). These cutoffs belong to the actual input vectors; the endomorphism-valued summand is not globally finitely supported. TensorProduct.lift gives the linear extension. Tensor induction proves lower truncation on every finite superposition. The fieldBilinear operation is separately additive and homogeneous in the two input fields. The identity field has its only normalized mode at minus one. Tensoring with it embeds the other factor's modes by TensorProduct.map; these embeddings are used in the proof of translation covariance.

This is reusable operator-field infrastructure for an even matter factor tensor a bc field. It does not assume a tensor VOA, a Koszul state-assignment rule, Jacobi, Borcherds identities, BRST classification, string dynamics or an AdS/CFT conclusion. The construction and its identities are derived from the input Laurent fields, not premises asserting the desired output field.

**Theorem 1.1 (Exact pointwise diagonal bounds).**

Lean statement: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.diagonal_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.diagonal_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two factor Laurent orders cut out a finite integer interval. Empty intervals give zero modes. There are no finite-dimensional, cutoff or positive-energy assumptions.

**Theorem 1.2 (Every algebraic tensor has a truncation bound).**

Lean statement: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.mode_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.mode_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pure tensors use upper(A,u)+upper(B,v)+1; sums use the maximum of the two previously obtained bounds. The result constructs an actual Laurent-series-valued linear map.

**Theorem 1.3 (Derivative Leibniz rule).**

Lean statement: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.derivative_leibniz`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.derivative_leibniz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative has normalized coefficient -n A_(n-1). The first-factor derivative is genuinely reindexed by i-1. The two weights -(i+1) and -(n-1-i) add to -n. Weighted finite support is proved before sum linearity.

**Theorem 1.4 (Translation acts by the sum of the two factor translations).**

Lean statement: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.translation_covariant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.translation_covariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each input field satisfies [T,A_n]=-n A_(n-1), the tensor field satisfies the same identity with T equal to T_U tensor id plus id tensor T_V. Each lifted translation is passed through a proved finite sum. The two commutators are then combined using the derivative Leibniz theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.derivative_leibniz`
- Truth anchor: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.diagonal_support`
- Truth anchor: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.mode_bounded`
- Truth anchor: `D5/S3/VertexAlgebra/VertexOperatorTensorProduct.translation_covariant`
