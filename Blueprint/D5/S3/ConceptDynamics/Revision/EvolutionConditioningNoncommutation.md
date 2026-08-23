# Evolution and Conditioning Noncommutation

## Abstract

Evolution and conditioning can fail to commute, but invariant evidence restores it.

**Theorem 1.1 (Evolution and conditioning need not commute).**

$$\exists X: Type, F: \operatorname{Set}\left(X\right) \to \operatorname{Set}\left(X\right), P, A: \operatorname{Set}\left(X\right),\ \operatorname{F}\left(\operatorname{conditioning}\left(P, A\right)\right) \neq \operatorname{conditioning}\left(P, \operatorname{F}\left(A\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation.evolution_and_conditioning_do_not_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is no general commutation law for conditioning and arbitrary set evolution: some carrier, set transformer, evidence set, and admitted-state set make condition-then-evolve differ from evolve-then-condition.

On the Boolean carrier, the saturating evolution sends a nonempty set to the entire carrier and the empty set to the empty set. With admitted states {false} and evidence {true}, conditioning first produces the empty set, whereas evolving first and then conditioning produces {true}.

**Theorem 1.2 (Invariant evidence restores commutation for image evolution).**

$$\forall X: Type, f: X \to X, P, A: \operatorname{Set}\left(X\right),\ \operatorname{preimage}\left(f, P\right) = P \Rightarrow \operatorname{imageEvolution}\left(f, \operatorname{conditioning}\left(P, A\right)\right) = \operatorname{conditioning}\left(P, \operatorname{imageEvolution}\left(f, A\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation.image_evolution_commutes_with_conditioning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any pointwise transition, if pulling the evidence set back along the transition returns the same evidence set, then direct-image evolution commutes with conditioning for every admitted-state set.

The invariance condition rewrites the evidence set as a preimage. The direct image of the resulting intersection is exactly the intersection of the evolved states with the evidence set, with no injectivity assumption on the transition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation.evolution_and_conditioning_do_not_commute`
- Truth anchor: `D5/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation.image_evolution_commutes_with_conditioning`
