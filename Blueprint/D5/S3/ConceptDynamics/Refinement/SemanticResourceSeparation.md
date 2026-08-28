# Semantic Sufficiency Beyond Finite Resources

## Abstract

More semantic targets than allowed algorithms force a resource-unreachable target.

**Theorem 1.1 (Semantic sufficiency can exceed finite resources).**

$$\begin{gathered}\forall X, B_{C}, Y: \operatorname{Type}, [\operatorname{Fintype}\left(Y\right)], [\operatorname{Nonempty}\left(Y\right)],\\{}C: X \to B_{C}, [\operatorname{Fintype}\left(\operatorname{range}\left(C\right)\right)], cost: ResourceCost, r\in \mathbb{N},\\{}A_{r}: \operatorname{Finset}\left(B_{C} \to Y\right),\\{}A_{r} = \{f: B_{C} \to Y \mid \operatorname{cost}\left(f\right) \le r\},\\{}\lvert Y \rvert^{\lvert \operatorname{range}\left(C\right) \rvert} > \lvert A_{r} \rvert \Rightarrow \exists T: X \to Y,\\{}\operatorname{Refines}\left(T, C\right) \land \neg \operatorname{ResourceRefines}\left(cost, r, T, C\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/SemanticResourceSeparation.semantic_sufficiency_can_exceed_finite_resources` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target carrier and the image of the concept readout are finite, and the target carrier is nonempty. The finite allowed class is exactly the class of factor maps whose declared cost is within budget.

Restricting every allowed factor to the readout image yields no more functions than there are allowed algorithms. The strict cardinality hypothesis therefore supplies a target function missing from those restrictions.

Composing that function with the readout constructs the target. Nonemptiness extends the function off the image, proving semantic refinement, while membership in the budget class would contradict how it was selected.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/SemanticResourceSeparation.semantic_sufficiency_can_exceed_finite_resources`
- Dependency: [D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition](ResourceRefinementComposition.md)
