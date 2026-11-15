# Components GateModel Algorithm Permutation

## Abstract

Addressed quantum circuit: Components GateModel Algorithm Permutation

**Definition 1.1 (cnotPermutation).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnotPermutation`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnotPermutation` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The row permutation of the model's fixed two-qubit CNOT.

**Lemma 1.2 (cnot operator ofPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnot_operator_ofPerm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnot_operator_ofPerm` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

This permutation interprets the actual native token with exact phase.

**Lemma 1.3 (cnotPermutation pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnotPermutation_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnotPermutation_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

CNOT acts on the ordered control and target values, with addition in Fin 2.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnotPermutation`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnotPermutation_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation.cnot_operator_ofPerm`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm](../Algorithm.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Operator](../../Gates/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator](../../QubitPrimitive/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation](../../../Core/Base/Gate/Unitary/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis](../../../Util/FinPow/BinaryBasis.md)
