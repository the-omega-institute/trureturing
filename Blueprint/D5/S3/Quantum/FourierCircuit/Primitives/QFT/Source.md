# Primitives QFT Source

## Abstract

Addressed quantum circuit: Primitives QFT Source

**Definition 1.1 (phaseAngle).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseAngle`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseAngle` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Rotation angle at the supplied separation in one recursive QFT stage.

**Definition 1.2 (phaseStep).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseStep`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseStep` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One native controlled phase on the leading qubit and selected tail qubit.

**Definition 1.3 (phasePrefix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phasePrefix`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phasePrefix` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The first supplied number of controlled phases, in their original order.

**Definition 1.4 (phaseLayer).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseLayer`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseLayer` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The full controlled-phase layer of a recursive stage.

**Definition 1.5 (leadingHadamard).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.leadingHadamard`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.leadingHadamard` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One native Hadamard instruction on the leading register position.

**Definition 1.6 (tailLayer).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.tailLayer`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.tailLayer` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Place an existing tail circuit after the leading qubit without allocating any system.

**Definition 1.7 (noSwap).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.noSwap`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.noSwap` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Recursive construction before its final wire reversal.

**Definition 1.8 (circuit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.circuit`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.circuit` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The complete canonical source circuit, including the final wire reversal.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.circuit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.leadingHadamard`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.noSwap`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseAngle`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseLayer`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phasePrefix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.phaseStep`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source.tailLayer`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Construction](../../Components/Gates/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Operator](../../Components/Gates/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Construction](../../Core/Base/Gate/Placement/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement](../../Core/Base/UnitaryCircuit/Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive](Source/Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse](Source/Reverse.md)
