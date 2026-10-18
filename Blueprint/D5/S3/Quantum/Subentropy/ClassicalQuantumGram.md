# Classical-quantum Gram realization

## Abstract

Square-root Gram realization of canonical classical-quantum record states.

The label and fragment coordinate types are arbitrary finite types. Zero probabilities, singular conditional states, repeated eigenvalues and different row and column dimensions are permitted. For Y_x=p_x rho_x, form the rectangular matrix V whose x-th column block is the positive square root of Y_x. Its two Gram products are used without identifying their ambient spaces.

**Definition 1.1 (Coordinate block pinching).**

Lean statement: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.blockPinch`

*Formalization.* `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.blockPinch` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

The map retains a matrix entry precisely when its two classical labels agree.

**Definition 1.2 (Rectangular row of square roots).**

Lean statement: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.cqRowSqrt`

*Formalization.* `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.cqRowSqrt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

The row block indexed by x is the positive square root of p_x rho_x.

**Theorem 1.3 (Row Gram product is the mixture).**

Lean statement: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.row_mul_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.row_mul_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For nonnegative ensemble weights, cqRowSqrt times its adjoint equals the sum of the weighted density matrices. Normalization of the weights is not required. This identity supplies both the conditional pinching-gap identification and the labelled POVM decomposition.

**Definition 1.4 (Canonical conditional subentropy).**

Lean statement: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.conditionalSubentropy`

*Formalization.* `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.conditionalSubentropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

Conditional subentropy is subentropy(recordState) minus subentropy(mixtureState).

**Theorem 1.5 (Conditional subentropy is a Gram pinching gap).**

Lean statement: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.cq_conditional_eq_pinchingGap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.cq_conditional_eq_pinchingGap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For the canonical recordState and mixtureState, conditional subentropy equals the block-pinching gap of V*V, where V=cqRowSqrt. The two rectangular Gram products have equal determinant-integral subentropy. The positive square-root identities identify the pinched Gram matrix with the record state and the row Gram matrix with the mixture state, including zero ensemble weights and singular fragments.

**Theorem 1.6 (Pure-state block gap and labelled upper bound).**

Lean statement: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.pure_block_pinching`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.pure_block_pinching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For every normalized vector v on the label-fragment product, the pinching gap equals classical subentropy of the block squared norms. For every label x, the same gap is bounded above by one minus that block norm. The equality follows by rectangular Gram invariance and pure-state subentropy zero. The labelled bound integrates the existing classical determinant-kernel estimate with its integrable inverse-square majorant.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.blockPinch`
- Truth anchor: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.conditionalSubentropy`
- Truth anchor: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.cqRowSqrt`
- Truth anchor: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.cq_conditional_eq_pinchingGap`
- Truth anchor: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.pure_block_pinching`
- Truth anchor: `D5/S3/Quantum/Subentropy/ClassicalQuantumGram.row_mul_adjoint`
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Subentropy/Basic](Basic.md)
- Dependency: [D5/S3/Quantum/Subentropy/DensityKernel](DensityKernel.md)
