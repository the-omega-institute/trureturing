# Primitives QFT Mathematics BitReverse

## Abstract

Addressed quantum circuit: Primitives QFT Mathematics BitReverse

**Definition 1.1 (qftSwapLeft).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Left wire of the indexth symmetric bit-reversal swap.

**Definition 1.2 (qftSwapRight).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapRight`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapRight` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Right wire of the indexth symmetric bit-reversal swap.

**Lemma 1.3 (qftSwapLeft ne right).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft_ne_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft_ne_right` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftSwapLeft_ne_right (n : Nat) (index : Fin (n / 2)) : qftSwapLeft n index ≠ qftSwapRight n index.

**Definition 1.4 (qftBitReverseLabelPrefix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Basis-label action of the first count symmetric swaps.

**Lemma 1.5 (qftBitReverseLabelPrefix invariant).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix_invariant` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

After the first count symmetric swaps, the outer count wires on each side contain their reversed source bits and every middle wire is unchanged.

**Lemma 1.6 (qftBitReverseLabel eq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabel_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabel_eq` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The complete symmetric SWAP network realizes the canonical bit-reversal permutation on computational-basis labels.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabelPrefix_invariant`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftBitReverseLabel_eq`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapLeft_ne_right`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/BitReverse.qftSwapRight`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Label](../../../Components/Gates/Swap/Label.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics](../Mathematics.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow](../../../Util/FinPow.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse](../../../Util/FinPow/BitReverse.md)
