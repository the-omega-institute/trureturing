# Core Base Accounting ResourcePool

## Abstract

Addressed quantum circuit: Core Base Accounting ResourcePool

**Definition 1.1 (ResourcePool).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ResourcePool`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ResourcePool` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A finite event ledger whose coordinates are fixed by the selected execution model.

**Definition 1.2 (singleton).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.singleton`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.singleton` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

A pool containing multiplicity copies of one event coordinate.

**Definition 1.3 (count).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The exact multiplicity of one event coordinate.

**Definition 1.4 (ofList).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Convert an actual event list into its literal multiplicity ledger.

**Lemma 1.5 (count zero).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_zero` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma count_zero {model : ExecutionModel} (event : Resource.Event model) : count event (0 : ResourcePool model) = 0.

**Lemma 1.6 (count singleton).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_singleton` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Count one native coordinate in an arbitrary singleton ledger.

**Lemma 1.7 (count add).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_add`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_add` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma count_add {model : ExecutionModel} (event : Resource.Event model) (left right : ResourcePool model) : count event (left + right) = count event left + count event right.

**Lemma 1.8 (count ofList).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_ofList`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_ofList` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma count_ofList {model : ExecutionModel} (event : Resource.Event model) (events : List (Resource.Event model)) : count event (ofList events) = List.count event events.

**Lemma 1.9 (ofList cons).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList_cons`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList_cons` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma ofList_cons {model : ExecutionModel} (event : Resource.Event model) (events : List (Resource.Event model)) : ofList (event :: events) = singleton event + ofList events.

**Lemma 1.10 (ofList append).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList_append`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList_append` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma ofList_append {model : ExecutionModel} (first second : List (Resource.Event model)) : ofList (first ++ second) = ofList first + ofList second.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ResourcePool`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_add`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_ofList`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_singleton`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.count_zero`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList_append`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.ofList_cons`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool.singleton`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/Event](Event.md)
