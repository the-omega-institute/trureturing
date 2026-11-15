# Core Base Gate Model

## Abstract

Addressed quantum circuit: Core Base Gate Model

For every GateModel model and Occurrence gate, QuantumAlg.GateModel.Occurrence.coordinate gate is model.coordinate gate.token. Its operator reindexes model.operator gate.token along the certified placement index equivalence; the occurrence does not supply an independently chosen matrix.

**Definition 1.1 (GateModel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.GateModel`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.GateModel` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

An elementary-gate language with fixed physical and unitary semantics.

**Definition 1.2 (Occurrence).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.Occurrence`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.Occurrence` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One occurrence of a gate from a specific model. No independently supplied operator, event count, depth or space claim is stored here.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.GateModel`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.Occurrence`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator](../Control/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../Layout/Signature.md)
