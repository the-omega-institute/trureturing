# Interaction Witness from Noncommuting Interventions

## Abstract

Independent translations commute, so an observed order defect excludes that model.

**Theorem 1.1 (Independent translations commute and defects exclude them).**

$$\forall X, U, Y: \operatorname{Type}, [\operatorname{AddCommGroup}(X)], F: U \to X \to X,\ {\forall a: U \to X, {\forall u: U, x: X, F_{u}(x) = x + a_{u}} \Rightarrow\\\forall u, v: U, F_{u} \circ F_{v} = F_{v} \circ F_{u}} \land {\forall T: X \to Y, u, v: U, \operatorname{Nonempty}({\{x: X \mid T(F_{u}(F_{v}(x))) \neq T(F_{v}(F_{u}(x)))\}}) \Rightarrow\\\neg \exists a: U \to X, \forall w: U, x: X, F_{w}(x) = x + a_{w}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/AbelianTranslationInteraction.abelian_translation_commutation_and_defect_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be an abelian group, U an intervention-index type, and F_u the intervention at u. The first public clause assumes the interventions are constructed from independently indexed displacements and proves that every pair commutes.

For a canonical concept readout T, the second public clause says that a nonempty set of states distinguished by the two intervention orders rules out every independent additive-translation representation.

This state-level mechanism is the rigorous interaction witness behind the source's drug-order, legal-measure, course-order, trauma-and-repair, and multiple-cause examples.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/AbelianTranslationInteraction.abelian_translation_commutation_and_defect_exclusion`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
