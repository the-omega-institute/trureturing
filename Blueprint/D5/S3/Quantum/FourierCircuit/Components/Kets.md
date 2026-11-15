# Components Kets

## Abstract

Addressed quantum circuit: Components Kets

**Definition 1.1 (invSqrt2).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

(sqrt 2)^-1 : ℂ, the ubiquitous normalization scalar.

**Lemma 1.2 (invSqrt2 mul self).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2_mul_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2_mul_self` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹.

**Lemma 1.3 (star invSqrt2).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/Kets.star_invSqrt2`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/Kets.star_invSqrt2` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma star_invSqrt2 : star invSqrt2 = invSqrt2.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Kets.invSqrt2_mul_self`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/Kets.star_invSqrt2`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized](../Core/Base/State/Normalized.md)
