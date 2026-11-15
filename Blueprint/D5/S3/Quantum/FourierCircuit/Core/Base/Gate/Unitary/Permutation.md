# Core Base Gate Unitary Permutation

## Abstract

Addressed quantum circuit: Core Base Gate Unitary Permutation

**Lemma 1.1 (ofPerm entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.ofPerm_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.ofPerm_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A permutation matrix compares the image of the row with the column.

**Lemma 1.2 (ofPerm mul).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.ofPerm_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.ofPerm_mul` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Operator multiplication reverses the row-permutation composition order.

**Lemma 1.3 (reindex ofPerm).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.reindex_ofPerm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.reindex_ofPerm` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Transporting a permutation operator conjugates its row permutation by the same equivalence.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.ofPerm_entry`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.ofPerm_mul`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Permutation.reindex_ofPerm`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator](../../Control/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../Unitary.md)
