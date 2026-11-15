# Primitives QFT Source LeadingEntries

## Abstract

Addressed quantum circuit: Primitives QFT Source LeadingEntries

**Lemma 1.1 (leading complement).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.leading_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.leading_complement` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma leading_complement (n : Nat) (row column : (layout (n + 1)).Basis) : let application.

**Lemma 1.2 (qftSource leading matrix entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The actual leading Hadamard has identity action on the full tail register.

**Lemma 1.3 (qftSource leading matrix cons).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_cons`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_cons` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Leading-bit coordinates expose Hadamard tensor identity, with no extra phase.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.leading_complement`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_cons`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/LeadingEntries.qftSource_leading_matrix_entry`
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/Construction](../../../Components/Gates/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Components/Gates/SingleQubit/Entries](../../../Components/Gates/SingleQubit/Entries.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Construction](../../../Core/Base/Gate/Placement/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation](../../../Core/Base/Gate/Placement/Permutation.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding](../../../Core/Base/Layout/Quantum/Embedding.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection](../../../Core/Base/Layout/Quantum/Selection.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../../../Core/Base/UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
