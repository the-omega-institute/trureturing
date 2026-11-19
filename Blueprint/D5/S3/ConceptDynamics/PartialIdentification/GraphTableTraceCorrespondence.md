# Graph-table trace correspondence

## Abstract

At a fixed exogenous state, a parent-ordered structural model is encoded by graph-local equation tables. One realization with an independent fixed seed preserves every hard-intervention outcome simultaneously.

The exogenous carrier of the realization is the full family of graph-local response tables. The realization keeps the original graph and certified order. Its equation reads the supplied table at the node and parent assignment; its explicit seed is fixed independently of the original initialization.

The arbitrary-start theorem compares two traces whose initial states may differ. Induction on the order propagates agreement over the processed prefix; the topological certificate supplies the parent locality needed at the next update.

**Definition 1.1 (Graph-table structural model).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.graphTableModel`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.graphTableModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The model uses the supplied parent graph and a table-valued shared exogenous state, with equation value r(v, pa) and the explicit seed as its initial state.

**Theorem 1.2 (Parent-ordered traces agree from arbitrary initial states).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.evaluation_witness_result_unique_from_arbitrary_start`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.evaluation_witness_result_unique_from_arbitrary_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one model, intervention, assignment, and exogenous state, any two EvaluationWitness traces along the certified complete order have the same final assignment even when their initial states differ.

**Theorem 1.3 (One graph-table seed serves every intervention world).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.graph_table_shared_seed_trace_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.graph_table_shared_seed_trace_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an original model M at one shared exogenous state u, encode each table entry by M.equation(v, pa, u). This single encoding serves every hard intervention and assignment. Every original-model trace, including the trace from M.initial(u), has the same completed output as the realized table-model trace from the fixed seed. The proof transports the original trace to the table model and then applies arbitrary-start uniqueness. This deterministic correspondence does not construct probability laws, a full seven-output compiler, nested interventions, or heterogeneous value types.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.evaluation_witness_result_unique_from_arbitrary_start`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.graphTableModel`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence.graph_table_shared_seed_trace_correspondence`
- Dependency: [D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics](../Causal/ParentOrderedStructuralEvaluationSemantics.md)
