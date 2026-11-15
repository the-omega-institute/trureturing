# Core Base Gate Placement

## Abstract

Addressed quantum circuit: Core Base Gate Placement

**Definition 1.1 (Application).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.Application`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.Application` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A native occurrence on exactly the selected physical wires of an ambient layout.

**Definition 1.2 (coordinate).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.coordinate`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.coordinate` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The native event coordinate remains fixed by the original gate token.

**Definition 1.3 (operator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.operator`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.operator` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Act on the selected systems and preserve the complete complementary subsystem.

**Lemma 1.4 (application operator entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.application_operator_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.application_operator_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Each matrix entry factors through the actual gate and identity on its full complement.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.Application`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.application_operator_entry`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.coordinate`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement.operator`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator](../Control/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model](Model.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding](../Layout/Quantum/Embedding.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection](../Layout/Quantum/Selection.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified](../Tensor/Certified.md)
