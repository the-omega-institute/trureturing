# Knowledge Closure under Fiber Implication

## Abstract

Knowledge is preserved by implications valid on the admissible evidence fiber; structural knowledge supplies robust knowledge, and a Boolean model separates fiber validity from global implication.

**Theorem 1.1 (Knowledge is closed under fiber-valid implication).**

$$\forall X \in Type, B \in Type, A \in X \to Prop, e \in X \to B, P \in X \to Prop, Q \in X \to Prop, a \in X,\; \left(\operatorname{robustKnowledge}\left(A, e, P, a\right) \land \operatorname{fiberImplication}\left(A, e, P, Q, a\right)\right) \Rightarrow \operatorname{robustKnowledge}\left(A, e, Q, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication.knowledge_closure_under_fiber_implication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fiber implication needs to carry P to Q only at admissible states whose evidence agrees with the anchor; it makes no claim about states outside that fiber.

Robust knowledge supplies P at the admissible anchor and throughout its admissible evidence fiber. Applying the fiber implication at the anchor and at each such state establishes robust knowledge of Q.

**Lemma 1.2 (Structural knowledge implies robust knowledge).**

$$\forall X \in Type, B \in Type, A \in X \to Prop, e \in X \to B, P \in X \to Prop, a \in X,\; \operatorname{structuralKnowledge}\left(A, e, P, a\right) \Rightarrow \operatorname{robustKnowledge}\left(A, e, P, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication.structural_knowledge_implies_robust_knowledge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Structural knowledge makes the predicate constant on every evidence fiber and records its truth at an admissible anchor. For any admissible state with the anchor's evidence, fiber constancy transfers the anchor truth to that state, which is precisely the remaining robust-knowledge condition.

**Lemma 1.3 (Fiber implication need not hold globally).**

$$X = Bool, B = Unit,\\{}\operatorname{robustKnowledge}\left(\Lambda x, x = true, \Lambda x, unit, \Lambda x, True, true\right) \land \left(\operatorname{fiberImplication}\left(\Lambda x, x = true, \Lambda x, unit, \Lambda x, True, \Lambda x, x = true, true\right) \land \left(\left(\neg \left(\forall x \in Bool,\; True \Rightarrow x = true\right)\right) \land \operatorname{robustKnowledge}\left(\Lambda x, x = true, \Lambda x, unit, \Lambda x, x = true, true\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication.fiber_implication_not_global_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take Boolean states with only true admissible, constant Unit evidence, P always true, and Q true exactly at the state true. The fiber implication is valid because its admissible fiber contains no counterexample, and both P and Q are robustly known at true. The ambient implication nevertheless fails at false, proving that fiber validity is strictly weaker than global validity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication.fiber_implication_not_global_counterexample`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication.knowledge_closure_under_fiber_implication`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication.structural_knowledge_implies_robust_knowledge`
- Dependency: [D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge](../BoundedKnowledge/ResourceMonotoneBoundedKnowledge.md)
- Dependency: [D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction](RobustKnowledgeConjunction.md)
