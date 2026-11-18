# Core Base Layout Quantum Embedding Composition

## Abstract

Addressed quantum circuit: Core Base Layout Quantum Embedding Composition

**Definition 1.1 (compose).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.compose`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.compose` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Compose two inclusions of the same physical wires.

**Lemma 1.2 (embedding ext).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_ext`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_ext` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Embeddings are determined by their actual position maps.

**Lemma 1.3 (complement eq iff).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_eq_iff` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma complement_eq_iff (placement : QuantumLayout.Embedding source target) (row column : target.Basis) : (placement.splitBasis row).2 = (placement.splitBasis column).2 ↔ ∀ position, position ∉ placement.selection → row position = column position.

**Lemma 1.4 (selected compose).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.selected_compose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.selected_compose` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma selected_compose (inner : QuantumLayout.Embedding source intermediate) (outer : QuantumLayout.Embedding intermediate target) (basis : target.Basis) : ((compose inner outer).splitBasis basis).1 = (inner.splitBasis (outer.splitBasis basis).1).1.

**Lemma 1.5 (complement compose).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_compose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_compose` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma complement_compose (inner : QuantumLayout.Embedding source intermediate) (outer : QuantumLayout.Embedding intermediate target) (row column : target.Basis) : ((compose inner outer).splitBasis row).2 = ((compose inner outer).splitBasis column).2 ↔ (inner.splitBasis (outer.splitBasis row).1).2 = (inner.splitBasis (outer.splitBasis column).1).2 ∧ (outer.splitBasis row).2 = (outer.splitBasis column).2.

**Lemma 1.6 (embedding lift compose).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_compose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_compose` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Nested physical inclusions have exactly the same full operator as their composition.

**Lemma 1.7 (embedding lift mul).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_mul` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Physical extension preserves multiplication, including every spectator block.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_compose`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.complement_eq_iff`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.compose`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_ext`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_compose`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.embedding_lift_mul`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Composition.selected_compose`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary](../../../Gate/Unitary.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Operator](Operator.md)
