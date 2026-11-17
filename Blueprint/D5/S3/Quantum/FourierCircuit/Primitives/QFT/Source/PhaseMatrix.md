# Primitives QFT Source PhaseMatrix

## Abstract

Addressed quantum circuit: Primitives QFT Source PhaseMatrix

**Lemma 1.1 (phaseStep binaryMatrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phaseStep_binaryMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phaseStep_binaryMatrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma phaseStep_binaryMatrix (oracles : OracleModel) (n : Nat) (offset : Fin n) (environment : oracles.Interpretation) : onBinaryLabels (phaseStep oracles n offset) environment = qftControlledPhaseOperator 0 offset.succ (phaseAngle offset.val).

**Lemma 1.2 (phasePrefix binaryMatrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phasePrefix_binaryMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phasePrefix_binaryMatrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma phasePrefix_binaryMatrix (oracles : OracleModel) (n count : Nat) (bounded : count ≤ n) (environment : oracles.Interpretation) : (onBinaryLabels (phasePrefix oracles n count bounded) environment : HilbertOperator (Qubits (n + 1))) = Matrix.diagonal (qftPhaseLayerFactorPrefix n count bounded).

**Lemma 1.3 (qftSource phase binaryMatrix entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.qftSource_phase_binaryMatrix_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.qftSource_phase_binaryMatrix_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The full native source phase layer has the original exact Fourier phase on every input label.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phasePrefix_binaryMatrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.phaseStep_binaryMatrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/PhaseMatrix.qftSource_phase_binaryMatrix_entry`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Operator](../../../Components/Gates/ControlledPhase/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../../../Core/Base/Gate/Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics](../Mathematics.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors](../Mathematics/PhaseFactors.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix](Matrix.md)
