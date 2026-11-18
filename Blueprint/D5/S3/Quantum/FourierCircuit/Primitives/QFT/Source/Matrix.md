# Primitives QFT Source Matrix

## Abstract

Addressed quantum circuit: Primitives QFT Source Matrix

**Definition 1.1 (onBinaryLabels).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.onBinaryLabels`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.onBinaryLabels` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Express the actual word's operator in the original big-endian integer labels.

**Lemma 1.2 (qftSource binaryMatrix seq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_binaryMatrix_seq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_binaryMatrix_seq` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Sequential native execution has the same operator composition order in binary labels.

**Lemma 1.3 (qftSource binaryMatrix identity).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_binaryMatrix_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_binaryMatrix_identity` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The empty native word remains the identity in the original binary labels.

**Lemma 1.4 (qftSource primitive binaryMatrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_primitive_binaryMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_primitive_binaryMatrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Each native source instruction has its original addressed operator under this projection.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.onBinaryLabels`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_binaryMatrix_identity`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_binaryMatrix_seq`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Matrix.qftSource_primitive_binaryMatrix`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex](../../../Core/Base/Gate/Unitary/Reindex.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive](Primitive.md)
