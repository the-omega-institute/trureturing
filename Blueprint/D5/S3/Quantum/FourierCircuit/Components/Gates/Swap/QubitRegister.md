# Components Gates Swap QubitRegister

## Abstract

Addressed quantum circuit: Components Gates Swap QubitRegister

**Definition 1.1 (qubitLayout).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitLayout`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitLayout` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The original ordered register of physical qubits.

**Lemma 1.2 (selected pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.selected_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.selected_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma selected_pair (basis : Fin width → Fin 2) : UnitaryCircuit.selectedInput layout (qubitLayout width) (positions left right distinct) (dimensions (qubitLayout width) left right distinct rfl rfl) basis = ![basis left, basis right].

**Lemma 1.3 (matching coordinates).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.matching_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.matching_coordinates` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma matching_coordinates (row column : Fin width → Fin 2) : (fun index => row (Equiv.swap left right index)) = column ↔ ![row right, row left] = ![column left, column right] ∧ (qubitLayout width).restrictComplementBasis (Finset.univ.map (positions left right distinct)) row = (qubitLayout width).restrictComplementBasis (Finset.univ.map (positions left right distinct)) column.

**Definition 1.4 (qubitCircuit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitCircuit`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitCircuit` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Execute all three CNOTs on the selected positions of the original register.

**Lemma 1.5 (swap qubitCircuit matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitCircuit_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitCircuit_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The full native word realizes the unchanged addressed SWAP, including exact phase.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.matching_coordinates`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitCircuit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.qubitLayout`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.selected_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/QubitRegister.swap_qubitCircuit_matrix`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap](../Swap.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Coordinates](Coordinates.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Physical](Physical.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection](../../../Core/Base/Layout/Quantum/Selection.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Entries](../../../Core/Base/UnitaryCircuit/Placement/Entries.md)
