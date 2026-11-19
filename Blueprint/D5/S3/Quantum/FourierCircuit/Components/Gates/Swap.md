# Components Gates Swap

## Abstract

Addressed quantum circuit: Components Gates Swap

**Definition 1.1 (layout).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.layout`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.layout` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The two physical qubits on which the local construction runs.

**Definition 1.2 (permutation).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.permutation`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.permutation` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The independent two-qubit exchange permutation, in the fixed big-endian basis.

**Lemma 1.3 (swap permutation pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.swap_permutation_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.swap_permutation_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The target exchanges both values, without an assumption on either input.

**Definition 1.4 (operator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.operator`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.operator` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The target acts coherently by exchanging the two basis coordinates.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.layout`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.operator`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.permutation`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.swap_permutation_pair`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation](../../Core/Base/Gate/Unitary/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../Core/Base/Layout/Signature.md)
