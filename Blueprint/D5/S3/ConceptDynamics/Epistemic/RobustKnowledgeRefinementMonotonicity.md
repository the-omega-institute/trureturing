# Robust Knowledge Refinement Monotonicity

## Abstract

Robust knowledge is monotone under evidence refinement.

**Theorem 1.1 (Evidence refinement preserves robust knowledge).**

$$\forall X, B, B': \operatorname{Type},\\{}Adm, P: X \to Prop, E: X \to B, E': X \to B', a: X,\\{}\operatorname{Refines}\left(E, E'\right) \land \operatorname{robustKnowledge}\left(Adm, E, P, a\right) \Rightarrow\\{}\operatorname{robustKnowledge}\left(Adm, E', P, a\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeRefinementMonotonicity.robust_knowledge_monotone_under_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admissibility predicate, coarse and refined evidence channels, proposition, and anchor are independent source primitives.

Refinement is the canonical factorization order: the coarse evidence channel factors through the refined channel. Robust knowledge is the established predicate requiring truth at the admissible anchor and throughout its admissible evidence fiber.

Equality of refined evidence values remains equality after the public factor map. Every refined anchor fiber is therefore contained in the coarse anchor fiber, where the proposition is already true.

Repository searches found the exact family primitives but no existing theorem combining them. Pinned Mathlib has generic factorization lemmas but no admissible anchored knowledge result.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeRefinementMonotonicity.robust_knowledge_monotone_under_refinement`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction](RobustKnowledgeConjunction.md)
