# Core Base Gate Placement Permutation

## Abstract

Addressed quantum circuit: Core Base Gate Placement Permutation

**Definition 1.1 (basisEquiv).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.basisEquiv`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.basisEquiv` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Read the model's ordered argument values and the full untouched complement.

**Definition 1.2 (liftPermutation).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.liftPermutation`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.liftPermutation` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Reassemble a local permutation result on the same physical wires and complement.

**Lemma 1.3 (liftPermutation eq iff).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.liftPermutation_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.liftPermutation_eq_iff` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Equality after the lifted action checks both local outputs and the whole complement.

**Lemma 1.4 (operator ofPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.operator_ofPerm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.operator_ofPerm` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

An exact permutation interpretation of the actual token determines its full ambient operator.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.basisEquiv`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.liftPermutation`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.liftPermutation_eq_iff`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation.operator_ofPerm`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model](../Model.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement](../Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation](../Unitary/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding](../../Layout/Quantum/Embedding.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Signature](../../Layout/Signature.md)
