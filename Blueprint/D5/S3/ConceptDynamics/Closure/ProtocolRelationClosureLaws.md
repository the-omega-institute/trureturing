# Protocol and Relation Closure Laws

## Abstract

The canonical protocol and relation closures satisfy all three closure laws.

**Theorem 1.1 (Both canonical closures are extensive, monotone, and idempotent).**

$$\forall X \in Type, O \in Type, Q \in \operatorname{Set}\left(\operatorname{Concept}\left(X, O\right)\right), Q2 \in \operatorname{Set}\left(\operatorname{Concept}\left(X, O\right)\right), R \in \operatorname{Set}\left(X \times X\right), R2 \in \operatorname{Set}\left(X \times X\right),\; Q \subseteq \operatorname{DefinitionClosure}\left(Q\right) \land \left(\left(Q \subseteq Q2 \Rightarrow \operatorname{DefinitionClosure}\left(Q\right) \subseteq \operatorname{DefinitionClosure}\left(Q2\right)\right) \land \left(\operatorname{DefinitionClosure}\left(\operatorname{DefinitionClosure}\left(Q\right)\right) = \operatorname{DefinitionClosure}\left(Q\right) \land \left(R \subseteq \operatorname{jointKernel}\left(\lambda f: \operatorname{RelationInvariantReadouts}\left(O, R\right), \operatorname{val}\left(f\right)\right) \land \left(\left(R \subseteq R2 \Rightarrow \operatorname{jointKernel}\left(\lambda f: \operatorname{RelationInvariantReadouts}\left(O, R\right), \operatorname{val}\left(f\right)\right) \subseteq \operatorname{jointKernel}\left(\lambda f: \operatorname{RelationInvariantReadouts}\left(O, R2\right), \operatorname{val}\left(f\right)\right)\right) \land \operatorname{jointKernel}\left(\lambda f: \operatorname{RelationInvariantReadouts}\left(O, \operatorname{jointKernel}\left(\lambda f: \operatorname{RelationInvariantReadouts}\left(O, R\right), \operatorname{val}\left(f\right)\right)\right), \operatorname{val}\left(f\right)\right) = \operatorname{jointKernel}\left(\lambda f: \operatorname{RelationInvariantReadouts}\left(O, R\right), \operatorname{val}\left(f\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Closure/ProtocolRelationClosureLaws.protocol_relation_closure_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DefinitionClosure is the repository's canonical protocol-family closure. The relation closure is constructed directly as the joint kernel of all RelationInvariantReadouts.

The public statement carries three protocol-side clauses followed by the corresponding three relation-side clauses: extensivity, monotonicity, and idempotence.

No new closure object is declared. The protocol laws reuse the frozen family theorem, while the relation laws follow from the canonical Galois primitives.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Closure/ProtocolRelationClosureLaws.protocol_relation_closure_laws`
- Dependency: [D5/S3/ConceptDynamics/Closure/SourceClosureThreeLaws](SourceClosureThreeLaws.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](../DefinitionEscape/DefinitionKernelGalois.md)
