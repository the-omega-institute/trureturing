# Components Gates ControlledPhase Placement

## Abstract

Addressed quantum circuit: Components Gates ControlledPhase Placement

**Lemma 1.1 (phase token diagonal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.phase_token_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.phase_token_diagonal` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma phase_token_diagonal (angle : Real) : ((AlgorithmGate.model.operator (.singleQubit (phaseGateOp angle))).val : HilbertOperator (QuantumSignature.qubits 1).register) = Matrix.diagonal (fun basis => if QuantumSignature.qubitsIndexEquiv 1 basis = 0 then 1 else Complex.exp ((angle : Complex) * Complex.I)).

**Lemma 1.2 (controlledPhase single phase diagonal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.controlledPhase_single_phase_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.controlledPhase_single_phase_diagonal` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Each actual phase occurrence acts on exactly the selected bit of the full two-qubit basis.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.controlledPhase_single_phase_diagonal`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Placement.phase_token_diagonal`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm](../../GateModel/Algorithm.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Construction](../Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Construction](Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/PhaseOperator](../PhaseOperator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Diagonal](../../../Core/Base/Gate/Placement/Diagonal.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
