# Util FinPow BitReverse

## Abstract

Addressed quantum circuit: Util FinPow BitReverse

**Definition 1.1 (qftReverseBits).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reverse the n significant bits of a computational-basis label.

**Lemma 1.2 (qftReverseBits testBit).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_testBit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_testBit` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftReverseBits_testBit (n : Nat) (label : Fin (2 ^ n)) (bit : Fin n) : (qftReverseBits n label).val.testBit bit.val = label.val.testBit (Fin.rev bit).val.

**Lemma 1.3 (qftReverseBits involutive).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_involutive` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftReverseBits_involutive (n : Nat) (label : Fin (2 ^ n)) : qftReverseBits n (qftReverseBits n label) = label.

**Definition 1.4 (qftReverseBitsPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBitsPerm`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBitsPerm` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Bit reversal as a self-inverse basis-label permutation.

**Definition 1.5 (qftPairEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Big-endian splitting of an (n+1)-qubit basis label into its leading bit and lower n-bit tail.

**Lemma 1.6 (qftPairEquiv apply val).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_apply_val`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_apply_val` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftPairEquiv_apply_val (n : Nat) (head : Fin 2) (tail : Fin (2 ^ n)) : (qftPairEquiv n (head, tail)).val = tail.val + 2 ^ n * head.val.

**Lemma 1.7 (qftPairEquiv testBit high).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_testBit_high`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_testBit_high` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftPairEquiv_testBit_high (n : Nat) (head : Fin 2) (tail : Fin (2 ^ n)) : (qftPairEquiv n (head, tail)).val.testBit n = decide (head = 1).

**Lemma 1.8 (qftPairEquiv mod tail).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_mod_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_mod_tail` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftPairEquiv_mod_tail (n : Nat) (head : Fin 2) (tail : Fin (2 ^ n)) : (qftPairEquiv n (head, tail)).val % 2 ^ n = tail.val.

**Lemma 1.9 (qftPairEquiv testBit low).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_testBit_low`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_testBit_low` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma qftPairEquiv_testBit_low (n : Nat) (head : Fin 2) (tail : Fin (2 ^ n)) (bit : Fin n) : (qftPairEquiv n (head, tail)).val.testBit bit.val = tail.val.testBit bit.val.

**Lemma 1.10 (qftReverseBits pair).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_pair` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Bit reversal moves the leading bit to the least-significant position and recursively reverses the lower label.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_apply_val`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_mod_tail`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_testBit_high`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftPairEquiv_testBit_low`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBitsPerm`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_involutive`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_pair`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow/BitReverse.qftReverseBits_testBit`
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow](../FinPow.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis](BinaryBasis.md)
