# Faithful Observation Commutation Criterion

## Abstract

Jointly faithful observations detect equality of two process orders.

**Theorem 1.1 (Faithful observations detect commutation).**

$$\begin{aligned}\forall I, X: \operatorname{Type}, Output: I \to \operatorname{Type},\\Q: \forall i: I, X \to \operatorname{Output}\left(i\right),\\Fu, Fv: X \to X,\\\operatorname{Injective}\left(\operatorname{jointReadout}\left(Q\right)\right) \land \\(\forall i: I, x: X, \operatorname{Q}\left(i, \operatorname{apply}\left(Fu, \operatorname{apply}\left(Fv, x\right)\right)\right) = \operatorname{Q}\left(i, \operatorname{apply}\left(Fv, \operatorname{apply}\left(Fu, x\right)\right)\right)) \implies\\Fu \circ Fv = Fv \circ Fu.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/FaithfulObservationCommutationCriterion.faithful_observation_commutation_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dependent family is assembled with the canonical jointReadout. Coordinatewise agreement of the two composite states therefore becomes equality of their joint readings.

Injectivity identifies those states for every input, and function extensionality identifies the composite processes.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/FaithfulObservationCommutationCriterion.faithful_observation_commutation_criterion`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](JointFaithfulnessLeibnizCriterion.md)
