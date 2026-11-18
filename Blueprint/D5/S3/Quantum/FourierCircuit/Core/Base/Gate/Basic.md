# Core Base Gate Basic

## Abstract

Addressed quantum circuit: Core Base Gate Basic

**Definition 1.1 (HilbertOperator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.HilbertOperator`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.HilbertOperator` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Raw linear operator over a finite quantum register.

**Definition 1.2 (applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.applyVec`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.applyVec` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Matrix-vector multiplication on raw state vectors.

**Lemma 1.3 (one applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.one_applyVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.one_applyVec` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma one_applyVec (ψ : HilbertVector R) : applyVec (1 : HilbertOperator R) ψ = ψ.

**Lemma 1.4 (mul applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.mul_applyVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.mul_applyVec` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma mul_applyVec (A B : HilbertOperator R) (ψ : HilbertVector R) : applyVec (A * B) ψ = applyVec A (applyVec B ψ).

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.HilbertOperator`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.applyVec`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.mul_applyVec`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic.one_applyVec`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized](../State/Normalized.md)
