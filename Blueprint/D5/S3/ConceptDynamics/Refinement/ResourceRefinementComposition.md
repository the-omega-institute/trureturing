# Resource Refinement Composition

## Abstract

Resource-bounded factorization witnesses compose under a monotone cost model.

**Definition 1.1 (Resource-bounded refinement).**

Lean statement: `D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition.ResourceRefines`

*Formalization.* `D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition.ResourceRefines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ResourceRefines is the source factorization relation with a public natural-valued budget: a recovery map witnesses the factorization and its cost is at most that budget.

**Theorem 1.2 (Resource refinement composes).**

$$\forall cost, \forall combine, \forall qC, \forall qD, \forall qE, \forall r, \forall s, compositionBound \land combineMono \land \operatorname{ResourceRefines}\left(cost, r, qC, qD\right) \land \operatorname{ResourceRefines}\left(cost, s, qD, qE\right) \Rightarrow {\operatorname{ResourceRefines}\left(cost, \operatorname{combine}\left(r, s\right), qC, qE\right) \land (\operatorname{combine}\left(r, s\right) = r+s) \Rightarrow \operatorname{ResourceRefines}\left(cost, r+s, qC, qE\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition.resource_refinement_compose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public cost-model hypotheses say that composing two recovery maps costs no more than the declared combination of their costs, and that the combination is monotone in each budget.

The composed recovery map is the ordinary function composite. The first conclusion gives the combined budget; when the model chooses the additive rule, the second conclusion gives the stated r + s budget.

The canonical Concept and factorization vocabulary is imported from the existing ConceptDynamics family; no sibling carrier or relation is redeclared.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition.ResourceRefines`
- Truth anchor: `D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition.resource_refinement_compose`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
