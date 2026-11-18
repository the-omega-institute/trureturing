# Rectangular Euclidean matrix transports

## Abstract

Rectangular matrix transports for the common positive-state scalarizer.

**Definition 1.1 (Matrix action as a continuous linear map).**

Lean statement: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM`

*Formalization.* `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite row and column carriers, the action of the complex rectangular matrix is transported to a continuous linear map between the corresponding Euclidean spaces. The Gram norm and Douglas factor estimates use this map.

**Theorem 1.2 (Gram order and adjoint norm).**

Lean statement: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.gram_majorization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.gram_majorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive semidefinite inequality k C C adjoint minus D D adjoint bounds the norm of D adjoint z by square root k times the norm of C adjoint z. It applies to different column spaces and to k=0.

**Theorem 1.3 (Adjoint transport).**

Lean statement: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euclidean continuous linear map of a conjugate transpose is the adjoint of the Euclidean continuous linear map. The rectangular factor and the supported Gram estimate use this identity.

**Theorem 1.4 (A rectangular factor with the prescribed bound).**

Lean statement: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.rectangular_douglas`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.rectangular_douglas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pad the two rectangular maps on the Euclidean Hilbert space over the disjoint sum of their column indices. The existing Douglas majorization theorem supplies an operator on that Hilbert space. Its off-diagonal block is a factor T with C T=D and norm at most square root k. Restriction and inclusion preserve the bound, including k=0. The common positive-state theorem applies this factor to its selected joint Gram.

**Theorem 1.5 (Composition transport).**

Lean statement: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Euclidean continuous linear maps carry matrix multiplication to composition. The projection of the rectangular factor uses this identity.

**Theorem 1.6 (Norm bounds as Gram order).**

Lean statement: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.norm_bound_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.norm_bound_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pointwise square root k norm bound implies positivity of k I minus T adjoint T. The common-state construction uses this estimate for the rectangular factor, the singular polar contraction and the supported Gram flip.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.gram_majorization`
- Truth anchor: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM`
- Truth anchor: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_adjoint`
- Truth anchor: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_mul`
- Truth anchor: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.norm_bound_gram`
- Truth anchor: `D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.rectangular_douglas`
- Dependency: [D5/S3/HilbertOperators/DouglasLemma](../../HilbertOperators/DouglasLemma.md)
