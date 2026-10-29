# The actual completed coefficient operator

## Abstract

The actual two-mode columns synthesize one Hilbert-Schmidt operator, and its product with its adjoint is the existing physical partial trace.

**Theorem 1.1 (The complete unique column-operator contract).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.exists_unique_completed_coefficient_operator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.exists_unique_completed_coefficient_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every completed two-mode V there exists exactly one continuous complex-linear C satisfying all occupation-column equations, the Hilbert-Schmidt property, the full Parseval square-sum equality and the identity purePartialTrace(V)=C*C-adjoint. Uniqueness follows from continuity and equality on the total occupation basis; no basis vector is replaced by zero padding.

**Theorem 1.2 (Hilbert-Schmidt synthesis of every column).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.exists_coefficient_operator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.exists_coefficient_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual two-mode V, there is a continuous complex-linear operator C on H taking the j-th occupation basis vector to V(j), for every natural j. C is Hilbert-Schmidt, and the complete sum of squared column norms equals norm(V)^2. The existing ColumnSynthesis theorem is used after reindexing the occupation Hilbert basis onto its range as a set of genuine Hilbert vectors.

**Theorem 1.3 (The existing reduced operator is C times C-adjoint).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.pure_partial_trace_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.pure_partial_trace_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V, purePartialTrace(V) equals coefficientOperator(V) times its Hilbert adjoint. The owner's partial trace is the full sum of rank-one operators of the actual columns. Absolute summability in operator norm and the occupation expansion of C-adjoint(y) identify both sides on every y in H. No finite-support or finite-rank assumption is imposed.

**Theorem 1.4 (Actual operator images give the evaluation sections).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.kernel_eq_coefficient_operator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.kernel_eq_coefficient_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V,z,w, the completed Bargmann kernel at (z,w) is the Bargmann transform at z of C applied to the actual exponential vector at w. The full vector-valued contraction converges in H. This identity fixes the column convention and supplies a genuine Hilbert section for each complex parameter.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.exists_coefficient_operator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.exists_unique_completed_coefficient_operator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.kernel_eq_coefficient_operator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.pure_partial_trace_eq`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis](../../Analysis/TraceClass/ColumnSynthesis.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel](BargmannKernel.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance](DisplacementCovariance.md)
