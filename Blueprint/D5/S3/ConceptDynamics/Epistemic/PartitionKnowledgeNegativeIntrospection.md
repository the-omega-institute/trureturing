# Partition Knowledge Negative Introspection

## Abstract

Knowledge defined on readout fibers recognizes its own failure.

**Definition 1.1 (Fiberwise knowledge).**

Lean statement: `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.fiberKnowledge`

*Formalization.* `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.fiberKnowledge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A predicate is known at a state when it holds at every state with the same readout value.

**Definition 1.2 (Readout partition topology).**

Lean statement: `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.partitionTopology`

*Formalization.* `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.partitionTopology` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout partition topology is induced from the discrete topology on the coordinate type, so its open sets are unions of readout fibers.

**Theorem 1.3 (Open failure and negative introspection).**

$$\begin{gathered}\forall X, B: \operatorname{Type}, C: X \to B, P\subset X,\\{}\operatorname{IsOpen}_{\tau_{C}}(X \setminus K_{C}(P)) \land\\{}(\forall x\in X, \neg(x\in K_{C}(P)) \Rightarrow x\in K_{C}(X \setminus K_{C}(P))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.partition_knowledge_negative_introspection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary state and coordinate types, the readout and predicate are independent source primitives. Fiberwise knowledge and the partition topology are constructed from that readout.

The public statement records both source clauses: the complement of the knowledge set is open, and every state where knowledge fails knows that failure throughout its whole readout fiber.

Pinned Mathlib supplies openness for induced discrete topologies. Negative introspection follows by transporting one failed fiber condition to every state with the same readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.fiberKnowledge`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.partitionTopology`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.partition_knowledge_negative_introspection`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
