# Util FinPow

## Abstract

Addressed quantum circuit: Util FinPow

**Definition 1.1 (prodEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow.prodEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Util/FinPow.prodEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Big-endian pairing of basis labels: (x, y) ↦ y + 2 ^ n * x, so the first (lower-qubit-index) factor carries the most significant bits.

**Lemma 1.2 (nat ofBits succ last).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/FinPow.nat_ofBits_succ_last`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/FinPow.nat_ofBits_succ_last` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reconstructing a natural number from n + 1 little-endian bits can be split into the lower n bits plus the final most-significant bit.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow.nat_ofBits_succ_last`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/FinPow.prodEquiv`
