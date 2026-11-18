# Core Base Gate Unitary Reindex

## Abstract

Addressed quantum circuit: Core Base Gate Unitary Reindex

**Lemma 1.1 (unitaryOperator reindex one).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_one` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Relabelling the identity gives the identity on the target register.

**Lemma 1.2 (unitaryOperator reindex mul).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_mul` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Exact operator composition commutes with a common change of basis labels.

**Lemma 1.3 (unitaryOperator reindex cancel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_cancel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_cancel` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Transporting back to the original basis restores the complete operator.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_cancel`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_mul`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex.unitaryOperator_reindex_one`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator](../../Control/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../Unitary.md)
