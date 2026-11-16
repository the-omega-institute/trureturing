# Primitives QFT Source Primitive

## Abstract

Addressed quantum circuit: Primitives QFT Source Primitive

**Definition 1.1 (sourceCircuit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive.sourceCircuit`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive.sourceCircuit` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One actual native source instruction on the declared pair of qubits.

**Lemma 1.2 (qftPrimitive sourceCircuit matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive.qftPrimitive_sourceCircuit_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive.qftPrimitive_sourceCircuit_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The primitive source gate has exactly the original addressed QFT operator.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive.qftPrimitive_sourceCircuit_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive.sourceCircuit`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier](../../../Components/GateModel/Fourier.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/QubitRegister](../../../Components/Gates/ControlledPhase/QubitRegister.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister](../../../Components/Gates/Swap/QubitRegister.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Construction](../../../Core/Base/Gate/Placement/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Native](../../../Core/Base/UnitaryCircuit/Realization/Native.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
