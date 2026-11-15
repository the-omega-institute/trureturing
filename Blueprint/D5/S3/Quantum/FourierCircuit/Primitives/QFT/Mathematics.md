# Primitives QFT Mathematics

## Abstract

Addressed quantum circuit: Primitives QFT Mathematics

For every natural n, the source constant QuantumAlg.ω n is exp((2 pi / 2^n) i). Its positive sign fixes the forward-transform convention, and n equal to zero is included.

**Lemma 1.1 (omega pow eq one).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_pow_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_pow_eq_one` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every natural n, ω_n ^ (2^n) = 1. This states that 2^n is a period.

**Definition 1.2 (invSqrtN).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

QFT normalization factor: 1/√(2^n), generalizing NormalizedVector.invSqrt2.

**Lemma 1.3 (invSqrtN succ).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN_succ` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Recursive normalization of the Fourier transform.

**Lemma 1.4 (omega succ sq).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_sq` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The root for an n-qubit transform is the square of the root for the next larger transform.

**Lemma 1.5 (omega succ pow half).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_half`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_half` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The halfway power of the (n+1)-qubit Fourier root is minus one.

**Lemma 1.6 (omega succ pow period mul).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_period_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_period_mul` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma omega_succ_pow_period_mul (n multiplier : Nat) : ω (n + 1) ^ (2 ^ (n + 1) * multiplier) = 1.

**Lemma 1.7 (qftOmega pair recurrence).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.qftOmega_pair_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.qftOmega_pair_recurrence` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Algebraic recurrence of the Fourier phase under the leading-bit/tail split.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.invSqrtN_succ`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_pow_eq_one`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_half`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_pow_period_mul`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.omega_succ_sq`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics.qftOmega_pair_recurrence`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Kets](../../Components/Kets.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../../Core/Base/Gate/Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Util/Complex](../../Util/Complex.md)
