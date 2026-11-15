# Components QubitPrimitive Operator

## Abstract

Addressed quantum circuit: Components QubitPrimitive Operator

**Definition 1.1 (QubitPrimitive).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.QubitPrimitive`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.QubitPrimitive` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Wire-addressed declarations for the common reversible qubit primitives.

**Definition 1.2 (applyLabel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.applyLabel`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.applyLabel` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Classical computational-basis action of one primitive declaration.

**Definition 1.3 (perm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Certified basis permutation of one primitive declaration.

**Lemma 1.4 (perm apply).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm_apply` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma perm_apply {n : Nat} (primitive : QubitPrimitive n) (label : Fin (2 ^ n)) : primitive.perm label = primitive.applyLabel label.

**Definition 1.5 (operator).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Canonical unitary operator of one addressed primitive declaration.

**Lemma 1.6 (operator apply ket).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator_apply_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator_apply_ket` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma operator_apply_ket {n : Nat} (primitive : QubitPrimitive n) (label : Fin (2 ^ n)) : primitive.operator.apply (NormalizedVector.ket label) = NormalizedVector.ket (primitive.applyLabel label).

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.QubitPrimitive`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.applyLabel`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator_apply_ket`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm_apply`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../../Core/Base/Gate/Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/WireAddress](../../Core/Base/WireAddress.md)
