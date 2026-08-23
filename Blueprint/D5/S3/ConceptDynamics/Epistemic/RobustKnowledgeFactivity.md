# Robust Knowledge Factivity

## Abstract

Robust knowledge entails truth at its evidence anchor.

**Theorem 1.1 (Knowledge is factual).**

$$\forall X, B: \operatorname{Type}, Adm, P: X \to Prop, E: X \to B, a: X,\\{}\operatorname{robustKnowledge}\left(Adm, E, P, a\right) \Rightarrow \operatorname{P}\left(a\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeFactivity.robust_knowledge_factivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let admissibility and the evidence channel be independent source primitives on an arbitrary state type, and let P be an arbitrary state predicate with anchor a.

If P is robustly known at a, then P holds at a. The imported robust knowledge predicate also records admissibility and stability over the entire evidence fiber, so the implication exposes its factual anchor clause without redefining knowledge.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeFactivity.robust_knowledge_factivity`
- Dependency: [D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction](RobustKnowledgeConjunction.md)
