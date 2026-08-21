# Robust Knowledge Conjunction

## Abstract

Evidence-fiber-stable knowledge is closed under conjunction.

**Definition 1.1 (Robust knowledge).**

Lean statement: `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction.robustKnowledge`

*Formalization.* `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction.robustKnowledge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A proposition is robustly known at an anchor when the anchor is admissible, the proposition holds there, and it holds at every admissible state with the same evidence.

**Theorem 1.2 (Knowledge conjunction).**

$$\forall X, B: \operatorname{Type}, Adm, P, Q: X \to Prop, E: X \to B, a: X,\\{}\operatorname{robustKnowledge}\left(Adm, E, P, a\right) \land \operatorname{robustKnowledge}\left(Adm, E, Q, a\right) \Rightarrow\\{}\operatorname{robustKnowledge}\left(Adm, E, {\Lambda x, \operatorname{P}\left(x\right) \land \operatorname{Q}\left(x\right)}, a\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction.robust_knowledge_conjunction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admissibility predicate, evidence map, proposition predicates, and anchor are independent source primitives.

If each proposition is true throughout the anchor's admissible evidence fiber, both propositions are true throughout that same fiber, so their conjunction is robustly known.

The proof directly unpacks the source predicate and introduces the two fiberwise facts; no witness structure or target-defined carrier is used.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction.robustKnowledge`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction.robust_knowledge_conjunction`
