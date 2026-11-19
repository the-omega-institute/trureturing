# Core Base Control Operator

## Abstract

Addressed quantum circuit: Core Base Control Operator

**Lemma 1.1 (reindex matrix mem unitaryGroup).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex_matrix_mem_unitaryGroup`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex_matrix_mem_unitaryGroup` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reindexing both axes of a square matrix by one equivalence preserves unitarity.

**Lemma 1.2 (reindex mem unitaryGroup).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex_mem_unitaryGroup`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex_mem_unitaryGroup` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma reindex_mem_unitaryGroup (e : R.Index ≃ S.Index) (U : UnitaryOperator R) : Matrix.reindex e e (U : HilbertOperator R) ∈ Matrix.unitaryGroup S.Index ℂ.

**Definition 1.3 (reindex).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Transport a certified unitary operator along a register-index equivalence.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex_matrix_mem_unitaryGroup`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator.reindex_mem_unitaryGroup`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../Gate/Unitary.md)
