# Core Base State Normalized

## Abstract

Addressed quantum circuit: Core Base State Normalized

**Definition 1.1 (NormalizedVector).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A unit vector over a finite register, with no preparation metadata.

**Definition 1.2 (ofVector).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Certify a raw vector once its norm-one proof is available.

**Lemma 1.3 (ext).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma ext {ψ φ : NormalizedVector R} (hvec : ∀ i, ψ i = φ i) : ψ = φ.

**Definition 1.4 (ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Computational-basis ket as a metadata-free normalized vector.

**Lemma 1.5 (ket apply).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma ket_apply (x i : R.Index) : ket x i = if i = x then 1 else 0.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/State/Basic](Basic.md)
