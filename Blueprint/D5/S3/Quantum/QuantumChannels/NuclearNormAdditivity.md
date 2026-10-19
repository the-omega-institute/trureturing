# Real rectangular nuclear-norm additivity

## Abstract

For nonzero real vector families and positive weights, nuclear-norm additivity holds exactly when their normalized Gram matrices agree.

**Theorem 1.1 (A real rectangular polar contraction).**

Lean statement: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.exists_real_rectangular_polar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.exists_real_rectangular_polar` (`✓ std3`). ∎

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

For any real rectangular matrix A, a contraction Z takes the positive square root of A transpose times A to A, and A and that square root have the same norm on every input vector. The construction descends the correspondence between their ranges to a linear isometry and composes it with orthogonal projection. Rectangular matrices, zero matrices and zero dimensional spaces are included.

**Definition 1.2 (The trace pairing).**

Lean statement: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.dualPairing`

*Formalization.* `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.dualPairing` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

The pairing is the real linear trace of the composite of the adjoint of Z with the Euclidean linear map associated with A. The norm on Z is the operator norm induced by the Euclidean norms.

**Theorem 1.3 (The trace norm is attained by a contraction).**

Lean statement: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_eq_max_dualPairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_eq_max_dualPairing` (`✓ std3`). ∎

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

The actual trace norm is the trace of the positive square root of A transpose times A, as defined by the frozen FiniteTraceDistance module. The theorem constructs a contraction attaining this trace pairing and proves that every contraction gives a pairing at most the trace norm. Its proof diagonalizes the positive square root, applies Cauchy-Schwarz to every eigenvector and uses the polar contraction for attainment. Duality is a conclusion of the proof, not a hypothesis.

**Definition 1.4 (Weighted rank-one expansions).**

Lean statement: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.weightedOuter`

*Formalization.* `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.weightedOuter` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

For a finite outcome type, weightedOuter is the sum of u times the real outer products x y transpose. The input and output index types are arbitrary finite types and may have different cardinalities.

**Theorem 1.5 (The weighted rank-one nuclear bound).**

Lean statement: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_weightedOuter_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_weightedOuter_le` (`✓ std3`). ∎

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

With nonnegative weights, the trace norm of the weighted outer-product sum is bounded by the sum of u times the product of the vector lengths. No vector is required to be nonzero for this inequality. This follows from the proved duality theorem and the contraction estimate for each pairing.

**Theorem 1.6 (Kopel's v2 Lemma 4).**

Lean statement: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_weightedOuter_eq_iff_normalized_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_weightedOuter_eq_iff_normalized_gram` (`✓ std3`). ∎

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

For nonzero finite real vector families and strictly positive weights, the nuclear bound is an equality if and only if every pair of normalized x vectors has the same real inner product as the corresponding pair of normalized y vectors. This is Lemma 4 of Eran Kopel's supplied v2 additions. Necessity uses a maximizing contraction, and sufficiency uses the common-contraction criterion of WeightedGramContraction together with the proved upper and lower dual bounds. Repeated and dependent vectors and arbitrary positive weights are allowed. No basis, independence, or distinctness hypothesis is introduced. This establishes the additivity lemma; the channel equality characterization of Theorem 5 has additional dependencies.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.dualPairing`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.exists_real_rectangular_polar`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_eq_max_dualPairing`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_weightedOuter_eq_iff_normalized_gram`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.traceNorm_weightedOuter_le`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity.weightedOuter`
- Dependency: [D5/S3/QuadraticForms/WeightedGramContraction](../../QuadraticForms/WeightedGramContraction.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
