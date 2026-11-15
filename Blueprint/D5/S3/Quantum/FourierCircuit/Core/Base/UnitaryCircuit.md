# Core Base UnitaryCircuit

## Abstract

Addressed quantum circuit: Core Base UnitaryCircuit

**Definition 1.1 (matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.matrix`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.matrix` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Exact, metadata-free unitary semantics of the actual construction.

**Definition 1.2 (eventTrace).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.eventTrace`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.eventTrace` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Ordered native occurrences, including every actual macro expansion.

**Definition 1.3 (eventCost).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.eventCost`

*Formalization.* `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.eventCost` (`✓ std3`).

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Literal model-relative event multiplicities from the same construction.

**Lemma 1.4 (ofList eventTrace eq eventCost).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.ofList_eventTrace_eq_eventCost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.ofList_eventTrace_eq_eventCost` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Forgetting order in the actual native trace yields exactly the circuit's event ledger.

**Lemma 1.5 (identity matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.identity_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.identity_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma identity_matrix : ((identity gates oracles layout).matrix environment) = 1.

**Lemma 1.6 (identity eventCost).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.identity_eventCost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.identity_eventCost` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma identity_eventCost : (identity gates oracles layout).eventCost = 0.

**Lemma 1.7 (native matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.native_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.native_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma native_matrix (application : GateModel.Application gates layout) : ((native (oracles.

**Lemma 1.8 (seq matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.seq_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.seq_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma seq_matrix (left right : UnitaryCircuit gates oracles layout) : (seq left right).matrix environment = right.matrix environment * left.matrix environment.

**Lemma 1.9 (parallel matrix raw).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.parallel_matrix_raw`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.parallel_matrix_raw` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Parallel syntax denotes the product of the two actual lifted operators.

**Lemma 1.10 (seq eventCost).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.seq_eventCost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.seq_eventCost` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma seq_eventCost (left right : UnitaryCircuit gates oracles layout) : (seq left right).eventCost = left.eventCost + right.eventCost.

**Lemma 1.11 (macroCall matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.macroCall_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.macroCall_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

lemma macroCall_matrix (name : String) (body : UnitaryCircuit gates oracles layout) : ((macroCall name body).matrix environment) = (body.matrix environment).

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.eventCost`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.eventTrace`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.identity_eventCost`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.identity_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.macroCall_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.native_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.ofList_eventTrace_eq_eventCost`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.parallel_matrix_raw`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.seq_eventCost`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit.seq_matrix`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool](Accounting/ResourcePool.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/State/Normalized](State/Normalized.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Construction](UnitaryCircuit/Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence](UnitaryCircuit/Sequence.md)
