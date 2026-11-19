# Core Base UnitaryCircuit Physical

## Abstract

Addressed quantum circuit: Core Base UnitaryCircuit Physical

For every injective physical map from Nat to Nat, the relabel constructions for QuantumLayout.Embedding, GateModel.Application, OracleModel.Application, UnitaryLeaf, UnitarySequence and UnitaryCircuit use that same map. Embeddings keep their logical position maps. Applications keep the actual native token or oracle query. The sequence recursion preserves identity, leaf, sequential, embedded and disjoint parallel constructors, and the circuit construction wraps that relocated sequence. The matrix and event-trace lemmas below compare those literal constructions.

**Lemma 1.1 (liftOperator relabel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.liftOperator_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.liftOperator_relabel` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

The same local operator acts on the same coordinate values after physical relocation.

**Lemma 1.2 (toUnitary relabel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.toUnitary_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.toUnitary_relabel` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Logical operators are unchanged because relocation preserves every coordinate value.

**Lemma 1.3 (eventTrace relabel).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.eventTrace_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.eventTrace_relabel` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

Relocation retains each original native and query occurrence in execution order.

**Lemma 1.4 (relabel matrix internal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix_internal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix_internal` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma relabel_matrix_internal (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (environment : oracles.Interpretation) : ((circuit.relabel physical).matrix environment) = (circuit.matrix environment).

**Lemma 1.5 (relabel matrix).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma relabel_matrix (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (environment : oracles.Interpretation) : ((circuit.relabel physical).matrix environment) = (circuit.matrix environment).

**Lemma 1.6 (relabel eventTrace internal).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace_internal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace_internal` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

private lemma relabel_eventTrace_internal (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (operations : ClassicalOpModel.

**Lemma 1.7 (relabel eventTrace).**

Lean statement: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace` (`✓ std3`). ∎

*Citation.* QudeLeap Team (2026). *Original recursive quantum Fourier circuit proof and native event counts*. URL: <https://github.com/QudeLeap/Lean-QuantumAlg/tree/971dc8be8a153a116b6d7cd748f984d545861b00>.

*Commentary.*

public lemma relabel_eventTrace (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (operations : ClassicalOpModel.

## References

- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.eventTrace_relabel`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.liftOperator_relabel`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace_internal`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix_internal`
- Truth anchor: `D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.toUnitary_relabel`
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement](../Gate/Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex](../Gate/Unitary/Reindex.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Operator](../Layout/Quantum/Embedding/Operator.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling](../Layout/Quantum/Relabeling.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Placement](../Oracle/Placement.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit](../UnitaryCircuit.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Construction](Construction.md)
- Dependency: [D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence](Sequence.md)
