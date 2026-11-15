# Core Base UnitaryCircuit Placement

## Abstract

Addressed quantum circuit: Core Base UnitaryCircuit Placement

**Definition 1.1 (addressPermutation).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.addressPermutation`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.addressPermutation` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private def addressPermutation : Equiv.Perm Nat.

**Lemma 1.2 (addressPermutation apply).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.addressPermutation_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.addressPermutation_apply` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma addressPermutation_apply (index : Fin small) : addressPermutation source target position (source.wire index).identity = (target.wire (position index)).identity.

**Definition 1.3 (relocatedPlacement).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.relocatedPlacement`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.relocatedPlacement` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private def relocatedPlacement : QuantumLayout.Embedding (source.relabel (addressPermutation source target position).toEmbedding) target.

**Definition 1.4 (operatorAt).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.operatorAt`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.operatorAt` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Extend the independent source operator by identity at the selected physical positions.

**Definition 1.5 (placeAt).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Relocate and embed the actual native construction at the selected dimension-correct wires.

**Lemma 1.6 (placeAt matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Placement preserves the full operator, including phase and all spectator coherences.

**Lemma 1.7 (placeAt eventTrace).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt_eventTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt_eventTrace` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Physical placement retains the exact native occurrence order.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.addressPermutation`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.addressPermutation_apply`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.operatorAt`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt_eventTrace`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.placeAt_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement.relocatedPlacement`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Operator](../Layout/Quantum/Embedding/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling](../Layout/Quantum/Relabeling.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical](Physical.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Placement](Realization/Placement.md)
