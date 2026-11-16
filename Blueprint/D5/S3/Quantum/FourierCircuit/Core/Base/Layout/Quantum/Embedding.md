# Core Base Layout Quantum Embedding

## Abstract

Addressed quantum circuit: Core Base Layout Quantum Embedding

**Definition 1.1 (Embedding).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.Embedding`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.Embedding` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

An ordered subsystem consists of the same physical wires in a larger layout.

**Definition 1.2 (selection).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selection`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selection` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The ambient positions occupied by the ordered subsystem.

**Definition 1.3 (positionEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.positionEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.positionEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Source order identifies the selected ambient positions without changing their values.

**Definition 1.4 (valueEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.valueEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.valueEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Dimension equality casts a local value without permuting the computational basis.

**Definition 1.5 (selectedBasisEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selectedBasisEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selectedBasisEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The selected subsystem basis in source order; every coordinate map is a dimension cast.

**Definition 1.6 (splitBasis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.splitBasis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.splitBasis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Split an ambient basis into the ordered subsystem and every untouched wire.

**Lemma 1.7 (embedding splitBasis selected value).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.embedding_splitBasis_selected_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.embedding_splitBasis_selected_value` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Splitting reads precisely the original basis value at each selected physical wire.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.Embedding`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.embedding_splitBasis_selected_value`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.positionEquiv`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selectedBasisEquiv`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.selection`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.splitBasis`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding.valueEquiv`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum](../Quantum.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection](Selection.md)
