# Core Base UnitaryCircuit Sequence

## Abstract

Addressed quantum circuit: Core Base UnitaryCircuit Sequence

**Definition 1.1 (UnitarySequence).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.UnitarySequence`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.UnitarySequence` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Unitary syntax indexed by its native language, granted queries and physical layout.

**Definition 1.2 (toUnitary).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.toUnitary`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.toUnitary` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Interpret the actual tree as a certified unitary. Later operations multiply on the left.

**Definition 1.3 (eventTrace).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.eventTrace`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.eventTrace` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Native execution occurrences, retaining sequential order and every macro expansion.

**Definition 1.4 (eventCost).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.eventCost`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.eventCost` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Symbolic native multiplicities from the same construction, without enumerating repeats.

**Lemma 1.5 (ofList flatten eventTraces).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.ofList_flatten_eventTraces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.ofList_flatten_eventTraces` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma ofList_flatten_eventTraces {model : ExecutionModel} (traces : List (List (Resource.Event model))) : ResourcePool.ofList traces.flatten = (traces.map ResourcePool.ofList).sum.

**Lemma 1.6 (ofList eventTrace eq eventCost).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.ofList_eventTrace_eq_eventCost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.ofList_eventTrace_eq_eventCost` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Forgetting event order gives exactly the symbolic native multiplicity ledger.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.UnitarySequence`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.eventCost`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.eventTrace`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.ofList_eventTrace_eq_eventCost`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.ofList_flatten_eventTraces`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence.toUnitary`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool](../Accounting/ResourcePool.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Control/Operator](../Control/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Operator](../Layout/Quantum/Embedding/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Leaf](Leaf.md)
