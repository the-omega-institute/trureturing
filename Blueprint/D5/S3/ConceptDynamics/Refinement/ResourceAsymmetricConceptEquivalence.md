# Resource-Asymmetric Concept Equivalence

## Abstract

A finite permutation can be concept-equivalent but resource-asymmetric.

**Theorem 1.1 (Ordinary concept equivalence need not be resource equivalence).**

$$\begin{gathered}\forall X: \operatorname{Type}, [\operatorname{Finite}(X)],\\{}\forall pi: X \equiv X, \forall cost: ResourceCost, \forall r: \mathbb{N},\\{}(\operatorname{cost}(pi) \leq r \land \neg(\operatorname{cost}(pi^{-1}) \leq r)) \Rightarrow \\{}(\operatorname{ConceptEquivalent}(id, pi) \land\\{}\operatorname{ResourceRefines}(cost, r, pi, id) \land\\{}\neg(\operatorname{ResourceRefines}(cost, r, id, pi))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/ResourceAsymmetricConceptEquivalence.ordinary_equivalence_does_not_imply_resource_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite carrier, the two public concepts are the identity readout and the readout given by a named permutation. Its canonical inverse recovers the identity, so the concepts mutually factor.

The resource premise uses one cost model and one budget. It places the forward permutation within that budget and its inverse outside the same budget.

The forward map directly witnesses resource refinement in one direction. Any factor witnessing the reverse direction must equal the inverse permutation, so its alleged budget bound contradicts the premise.

All three clauses are public: ordinary equivalence, positive forward resource refinement, and failed reverse resource refinement. The cost and refinement relations are imported family primitives.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/ResourceAsymmetricConceptEquivalence.ordinary_equivalence_does_not_imply_resource_equivalence`
- Dependency: [D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence](../Interventions/RedundantAppealDefectPersistence.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition](ResourceRefinementComposition.md)
