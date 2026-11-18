# Components GateModel Fourier

## Abstract

Addressed quantum circuit: Components GateModel Fourier

**Definition 1.1 (Coordinate).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.Coordinate`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.Coordinate` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The three independently counted Fourier instructions.

**Definition 1.2 (Token).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.Token`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.Token` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A controlled-phase token retains its full angle, including its sign.

**Definition 1.3 (signature).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.signature`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.signature` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A Hadamard acts on one qubit; each phase or SWAP acts on two qubits.

**Definition 1.4 (coordinate).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.coordinate`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.coordinate` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Count source instructions without discarding their operator parameters.

**Definition 1.5 (operator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.operator`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.operator` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Exact local operators, with no identification modulo global phase.

**Definition 1.6 (model).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.model`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.model` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The natural native language of the canonical Fourier construction.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.Coordinate`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.Token`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.coordinate`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.model`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.operator`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/GateModel/Fourier.signature`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Construction](../Gates/ControlledPhase/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Operator](../Gates/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap](../Gates/Swap.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model](../../Core/Base/Gate/Model.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../Core/Base/Layout/Signature.md)
