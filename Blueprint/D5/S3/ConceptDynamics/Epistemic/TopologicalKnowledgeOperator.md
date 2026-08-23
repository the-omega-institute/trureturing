# Topological Knowledge Operator

## Abstract

Topological interior satisfies the four knowledge-operator laws.

**Theorem 1.1 (Interior is a topological knowledge operator).**

$$\forall X: \operatorname{Type},\\{}\operatorname{TopologicalSpace}(X) \Rightarrow\\{}(\forall P: \operatorname{Set}(X), \operatorname{interior}(P) \subseteq P) \land\\{}(\forall P, Q: \operatorname{Set}(X), P \subseteq Q \Rightarrow \operatorname{interior}(P) \subseteq \operatorname{interior}(Q)) \land\\{}(\forall P, Q: \operatorname{Set}(X), \operatorname{interior}(\operatorname{intersection}(P, Q)) = \operatorname{intersection}(\operatorname{interior}(P), \operatorname{interior}(Q))) \land\\{}(\forall P: \operatorname{Set}(X), \operatorname{interior}(\operatorname{interior}(P)) = \operatorname{interior}(P)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/TopologicalKnowledgeOperator.topological_knowledge_operator_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The knowledge operator is the canonical interior operation of the given topology; it is not defined from any target law.

The public statement separately exposes factivity, monotonicity, finite-intersection preservation, and positive introspection.

Each conjunct directly applies the corresponding pinned library law for topological interior.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/TopologicalKnowledgeOperator.topological_knowledge_operator_laws`
