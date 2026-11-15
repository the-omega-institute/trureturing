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

**Definition 1.5 (backward).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backward`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backward` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private abbrev backward : GateModel.Application AlgorithmGate.model layout.

**Definition 1.6 (backwardPermutation).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backwardPermutation`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backwardPermutation` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private def backwardPermutation : Equiv.Perm layout.Basis.

**Lemma 1.7 (backward pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backward_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backward_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma backward_pair (left right : Fin 2) : backwardPermutation ![left, right] = ![left + right, right].

**Lemma 1.8 (native permutation word).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.native_permutation_word`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.native_permutation_word` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma native_permutation_word : (AlgorithmGate.cnotPermutation.trans backwardPermutation).trans AlgorithmGate.cnotPermutation = permutation.

**Definition 1.9 (circuit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.circuit`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.circuit` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Execute the full forward/backward/forward CNOT word as one descriptive macro.

**Lemma 1.10 (swap circuit matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.swap_circuit_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.swap_circuit_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The three actual CNOTs realize the independent SWAP operator with exact phase.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backward`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backwardPermutation`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.backward_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.circuit`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.layout`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.native_permutation_word`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.operator`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.permutation`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.swap_circuit_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Gates/Swap.swap_permutation_pair`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation](../GateModel/Algorithm/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Construction](Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Canonical](../../Core/Base/Gate/Placement/Canonical.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation](../../Core/Base/Gate/Placement/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding](../../Core/Base/Layout/Quantum/Embedding.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../Core/Base/Layout/Signature.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis](../../Util/FinPow/BinaryBasis.md)
