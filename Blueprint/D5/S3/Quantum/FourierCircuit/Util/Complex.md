# Util Complex

## Abstract

Addressed quantum circuit: Util Complex

**Lemma 1.1 (conj exp I).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/Complex.conj_exp_I`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/Complex.conj_exp_I` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma conj_exp_I (φ : ℝ) : starRingEnd ℂ (Complex.exp (φ * Complex.I)) = Complex.exp (-(φ * Complex.I)).

**Lemma 1.2 (exp I mul exp neg I).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/Complex.exp_I_mul_exp_neg_I`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/Complex.exp_I_mul_exp_neg_I` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma exp_I_mul_exp_neg_I (φ : ℝ) : Complex.exp (φ * Complex.I) * Complex.exp (-(φ * Complex.I)) = 1.

**Lemma 1.3 (exp neg I mul exp I).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Util/Complex.exp_neg_I_mul_exp_I`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Util/Complex.exp_neg_I_mul_exp_I` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma exp_neg_I_mul_exp_I (φ : ℝ) : Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/Complex.conj_exp_I`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/Complex.exp_I_mul_exp_neg_I`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Util/Complex.exp_neg_I_mul_exp_I`
