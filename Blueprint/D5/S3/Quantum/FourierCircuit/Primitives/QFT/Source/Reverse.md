# Primitives QFT Source Reverse

## Abstract

Addressed quantum circuit: Primitives QFT Source Reverse

**Definition 1.1 (swapStep).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.swapStep`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.swapStep` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

One native SWAP exchanging the selected symmetric pair.

**Definition 1.2 (identityPlacement).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.identityPlacement`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.identityPlacement` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private def identityPlacement {count : Nat} (physical : QuantumLayout count) : QuantumLayout.Embedding physical physical.

**Definition 1.3 (localSwap).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.localSwap`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.localSwap` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Execute the exact same occurrence on only its own two physical systems.

**Lemma 1.4 (localSwap matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.localSwap_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.localSwap_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma localSwap_matrix (oracles : OracleModel) (n : Nat) (index : Fin (n / 2)) (environment : oracles.Interpretation) : ((localSwap oracles n index).matrix environment) = (application n index).occurrence.operator.

**Definition 1.5 (word).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.word`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.word` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Grow the real disjoint SWAP layer inside exactly its active physical subsystem.

**Lemma 1.6 (word eventTrace).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.word_eventTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.word_eventTrace` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma word_eventTrace (oracles : OracleModel) (n count : Nat) (bounded : count ≤ n / 2) : (word oracles n count bounded).eventTrace = List.replicate count (Resource.Event.gate (model.

**Definition 1.7 (reversePrefix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The first supplied symmetric pairs execute as one disjoint native layer.

**Lemma 1.8 (reversePrefix zero matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_zero_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_zero_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A zero-pair prefix is exactly identity on the complete bank.

**Lemma 1.9 (reversePrefix succ matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_succ_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_succ_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The parallel extension has the same full operator order as the next symmetric swap.

**Lemma 1.10 (reversePrefix eventTrace).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_eventTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_eventTrace` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Every symmetric SWAP remains present in the actual event traversal.

**Definition 1.11 (bitReverse).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.bitReverse`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.bitReverse` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The complete symmetric reversal is one parallel layer on the original bank.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.bitReverse`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.identityPlacement`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.localSwap`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.localSwap_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_eventTrace`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_succ_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.reversePrefix_zero_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.swapStep`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.word`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse.word_eventTrace`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition](../../../Core/Base/Layout/Quantum/Embedding/Composition.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Placement](../../../Core/Base/UnitaryCircuit/Realization/Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive](Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout](Reverse/Layout.md)
