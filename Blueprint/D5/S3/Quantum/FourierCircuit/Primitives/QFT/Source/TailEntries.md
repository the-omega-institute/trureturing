# Primitives QFT Source TailEntries

## Abstract

Addressed quantum circuit: Primitives QFT Source TailEntries

**Lemma 1.1 (tail complement).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.tail_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.tail_complement` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma tail_complement (n : Nat) (row column : (layout (n + 1)).Basis) : (layout (n + 1)).restrictComplementBasis (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) row = (layout (n + 1)).restrictComplementBasis (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) column ↔ row 0 = column 0.

**Lemma 1.2 (qftSource tail matrix entry).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_entry` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Placing the recursive word leaves precisely the leading coordinate untouched.

**Lemma 1.3 (qftSource tail matrix cons).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_cons`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_cons` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

In leading-bit and tail coordinates, the placed word is identity tensor its original matrix.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_cons`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.qftSource_tail_matrix_entry`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries.tail_complement`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection](../../../Core/Base/Layout/Quantum/Selection.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Entries](../../../Core/Base/UnitaryCircuit/Placement/Entries.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Primitive](../Primitive.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source](../Source.md)
