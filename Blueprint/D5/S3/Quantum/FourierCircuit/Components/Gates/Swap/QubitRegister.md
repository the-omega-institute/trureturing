# Components Gates Swap QubitRegister

## Abstract

Addressed quantum circuit: Components Gates Swap QubitRegister

**Definition 1.1 (qubitLayout).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitLayout`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitLayout` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The original ordered register of physical qubits.

**Lemma 1.2 (swap qubitOperator matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitOperator_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitOperator_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The placed SWAP has the unchanged addressed target, including exact phase.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitLayout`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitOperator_matrix`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap](../Swap.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates](Coordinates.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical](Physical.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection](../../../Core/Base/Layout/Quantum/Selection.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Entries](../../../Core/Base/UnitaryCircuit/Placement/Entries.md)
