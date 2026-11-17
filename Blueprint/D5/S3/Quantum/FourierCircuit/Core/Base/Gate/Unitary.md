# Core Base Gate Unitary

## Abstract

Addressed quantum circuit: Core Base Gate Unitary

**Definition 1.1 (UnitaryOperator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.UnitaryOperator`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.UnitaryOperator` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A unitary Hilbert operator over R, with no implementation metadata.

**Definition 1.2 (ofMatrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofMatrix`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofMatrix` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Certify a raw matrix once its unitarity proof is available.

**Definition 1.3 (applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.applyVec`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.applyVec` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A unitary operator still acts linearly on arbitrary raw vectors.

**Lemma 1.4 (one applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.one_applyVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.one_applyVec` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma one_applyVec (ψ : HilbertVector R) : (1 : UnitaryOperator R).applyVec ψ = ψ.

**Lemma 1.5 (mul applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.mul_applyVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.mul_applyVec` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma mul_applyVec (U V : UnitaryOperator R) (ψ : HilbertVector R) : (U * V).applyVec ψ = U.applyVec (V.applyVec ψ).

**Lemma 1.6 (inner applyVec applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.inner_applyVec_applyVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.inner_applyVec_applyVec` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Unitary operators preserve inner products on arbitrary vectors.

**Lemma 1.7 (norm applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.norm_applyVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.norm_applyVec` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Unitary operators preserve norms on arbitrary vectors.

**Definition 1.8 (apply).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.apply`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.apply` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A unitary operator maps normalized vectors to normalized vectors.

**Definition 1.9 (ofPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Unitary permutation operator on computational-basis labels.

**Lemma 1.10 (ofPerm applyVec).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_applyVec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_applyVec` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A certified permutation operator sends a basis ket to the inverse image of its label.

**Lemma 1.11 (ofPerm applyVec ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_applyVec_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_applyVec_ket` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma ofPerm_applyVec_ket (σ : Equiv.Perm R.Index) (x : R.Index) : (ofPerm σ).applyVec (NormalizedVector.ket x : HilbertVector R) = (NormalizedVector.ket (σ⁻¹ x) : HilbertVector R).

**Lemma 1.12 (ofPerm apply ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_apply_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_apply_ket` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A certified permutation preserves normalization while relabelling a ket.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.UnitaryOperator`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.apply`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.applyVec`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.inner_applyVec_applyVec`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.mul_applyVec`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.norm_applyVec`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofMatrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_applyVec`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_applyVec_ket`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.ofPerm_apply_ket`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary.one_applyVec`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Basic](Basic.md)
