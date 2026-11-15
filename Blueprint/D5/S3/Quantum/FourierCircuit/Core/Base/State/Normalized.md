# Core Base State Normalized

## Abstract

Addressed quantum circuit: Core Base State Normalized

**Definition 1.1 (instCoeHilbertVector).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeHilbertVector`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeHilbertVector` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every register R, a NormalizedVector R coerces to its underlying HilbertVector R through the vec field.

**Definition 1.2 (instCoeTailHilbertVector).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeTailHilbertVector`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeTailHilbertVector` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every register R, the tail coercion from NormalizedVector R to HilbertVector R is the vec field.

**Definition 1.3 (instCoeOutHilbertVector).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeOutHilbertVector`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeOutHilbertVector` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every register R, the output coercion from NormalizedVector R to HilbertVector R is the vec field.

**Definition 1.4 (instCoeFunForallIndexComplex).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeFunForallIndexComplex`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeFunForallIndexComplex` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

For every register R and normalized vector psi, function coercion evaluates psi.vec at an index of R. This supplies the notation used by ext and ket_apply.

**Definition 1.5 (NormalizedVector).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A unit vector over a finite register, with no preparation metadata.

**Definition 1.6 (ofVector).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Certify a raw vector once its norm-one proof is available.

**Lemma 1.7 (ext).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma ext {ψ φ : NormalizedVector R} (hvec : ∀ i, ψ i = φ i) : ψ = φ.

**Definition 1.8 (ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Computational-basis ket as a metadata-free normalized vector.

**Lemma 1.9 (ket apply).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma ket_apply (x i : R.Index) : ket x i = if i = x then 1 else 0.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.NormalizedVector`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ext`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeFunForallIndexComplex`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeHilbertVector`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeOutHilbertVector`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.instCoeTailHilbertVector`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ket_apply`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized.ofVector`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/State/Basic](Basic.md)
