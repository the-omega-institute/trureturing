# Primitives QFT Source Reverse Layout

## Abstract

Addressed quantum circuit: Primitives QFT Source Reverse Layout

**Definition 1.1 (swapLeft).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swapLeft`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swapLeft` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The lower position of a symmetric pair in the final wire reversal.

**Definition 1.2 (swapRight).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swapRight`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swapRight` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The upper position of the same symmetric pair.

**Lemma 1.3 (swap distinct).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swap_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swap_distinct` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma swap_distinct (n : Nat) (index : Fin (n / 2)) : swapLeft n index ≠ swapRight n index.

**Definition 1.4 (positions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.positions`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.positions` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Each prefix position names precisely one original outer physical wire.

**Definition 1.5 (subsystem).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.subsystem`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.subsystem` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The subsystem carries the same physical wire records as the complete bank.

**Definition 1.6 (complete).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.complete`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.complete` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Include exactly the prefix subsystem in the original bank.

**Definition 1.7 (pairPositions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.pairPositions`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.pairPositions` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Ordered positions of the next actual symmetric pair.

**Definition 1.8 (application).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.application`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.application` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The original native SWAP occurrence, with its complete ambient placement.

**Definition 1.9 (pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.pair`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.pair` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The next pair's actual two-wire layout contains no other bank system.

**Definition 1.10 (earlierPositions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlierPositions`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlierPositions` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Earlier outer wires occupy the corresponding positions in the enlarged prefix.

**Lemma 1.11 (earlier positions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier_positions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier_positions` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Enlarging the active subsystem keeps every earlier physical position.

**Definition 1.12 (earlier).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The earlier prefix is included without changing any wire record.

**Definition 1.13 (nextPositions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.nextPositions`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.nextPositions` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The new pair fills the last position of each outer half.

**Lemma 1.14 (next positions).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next_positions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next_positions` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The two new subsystem positions are exactly the next original symmetric pair.

**Definition 1.15 (next).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The next pair's actual physical wires occur at those two new positions.

**Lemma 1.16 (disjoint).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.disjoint` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Every earlier physical wire differs from both wires of the next pair.

**Lemma 1.17 (earlier complete).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier_complete` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Composing earlier-prefix placements gives the original complete-bank inclusion.

**Lemma 1.18 (next complete).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next_complete` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Composing the new pair's placements gives the original addressed native occurrence.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.application`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.complete`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.disjoint`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlierPositions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier_complete`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.earlier_positions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.nextPositions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next_complete`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.next_positions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.pairPositions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.positions`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.subsystem`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swapLeft`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swapRight`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Reverse/Layout.swap_distinct`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Construction](../../../../Core/Base/Gate/Placement/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition](../../../../Core/Base/Layout/Quantum/Embedding/Composition.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Primitive](../Primitive.md)
