# Components Gates ControlledPhase QubitRegister

## Abstract

Addressed quantum circuit: Components Gates ControlledPhase QubitRegister

**Definition 1.1 (qubitLayout).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.qubitLayout`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.qubitLayout` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The original ordered register of the supplied number of physical qubits.

**Definition 1.2 (qubitCircuit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.qubitCircuit`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.qubitCircuit` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Execute the full native word at two distinct positions of the original qubit register.

**Lemma 1.3 (controlledPhase qubitCircuit matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.controlledPhase_qubitCircuit_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.controlledPhase_qubitCircuit_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The native implementation realizes the unchanged addressed target on every register state.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.controlledPhase_qubitCircuit_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.qubitCircuit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister.qubitLayout`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Construction](Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Coordinates](Coordinates.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Physical](Physical.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Diagonal](../../../Core/Base/UnitaryCircuit/Placement/Diagonal.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Entries](../../../Core/Base/UnitaryCircuit/Placement/Entries.md)
