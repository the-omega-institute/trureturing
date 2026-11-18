# Core Base Layout Quantum Selection

## Abstract

Addressed quantum circuit: Core Base Layout Quantum Selection

**Definition 1.1 (SelectedPosition).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.SelectedPosition`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.SelectedPosition` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The original positions of the selected physical wires.

**Definition 1.2 (SelectedBasis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.SelectedBasis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.SelectedBasis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One local finite value at each selected original position.

**Definition 1.3 (ComplementBasis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.ComplementBasis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.ComplementBasis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One local finite value at every position outside the selection.

**Definition 1.4 (selectedRegister).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.selectedRegister`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.selectedRegister` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The selected register uses the exact dependent product of local bases.

**Definition 1.5 (complementRegister).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.complementRegister`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.complementRegister` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The complementary register contains all unselected original positions.

**Definition 1.6 (restrictSelectedBasis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.restrictSelectedBasis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.restrictSelectedBasis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Read the original basis value at each selected position.

**Definition 1.7 (restrictComplementBasis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.restrictComplementBasis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.restrictComplementBasis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Read the original basis value at every complementary position.

**Definition 1.8 (joinSelectedBasis).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reassemble a label by membership of each original physical position.

**Lemma 1.9 (joinSelectedBasis selected value).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis_selected_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis_selected_value` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reassembly restores the full finite value at every selected physical wire.

**Lemma 1.10 (joinSelectedBasis complement value).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis_complement_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis_complement_value` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reassembly restores the full finite value at every complementary wire.

**Definition 1.11 (selectionBasisEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.selectionBasisEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.selectionBasisEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Selection and complement give an exact basis equivalence by restriction.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.ComplementBasis`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.SelectedBasis`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.SelectedPosition`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.complementRegister`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis_complement_value`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.joinSelectedBasis_selected_value`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.restrictComplementBasis`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.restrictSelectedBasis`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.selectedRegister`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection.selectionBasisEquiv`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum](../Quantum.md)
