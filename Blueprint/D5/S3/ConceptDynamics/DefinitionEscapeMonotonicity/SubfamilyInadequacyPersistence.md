# Subfamily Inadequacy Persistence

## Abstract

Target inadequacy for a full readout family persists under every subfamily restriction.

**Theorem 1.1 (No subfamily repairs full-family inadequacy).**

$$\begin{aligned}\forall I, X, Y: \operatorname{Type},\\V: I \to \operatorname{Type}, q: \forall i: I, X \to \operatorname{V}\left(i\right),\\T: X \to Y,\\\neg (\operatorname{TargetAdequate}\left(\operatorname{jointReadout}\left(q\right), T\right)) \Rightarrow \forall J \subseteq I, \neg (\operatorname{TargetAdequate}\left(\operatorname{jointReadout}\left(\operatorname{restrict}\left(q, J\right)\right), T\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyInadequacyPersistence.full_family_inadequacy_persists_to_subfamilies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a dependent family of readouts on X and let T be a target. The full observation is the imported jointReadout q; the observation associated with a subset J is the same jointReadout instantiated on the subtype J.

Any decoder from the restricted readout also decodes from the full readout after restricting a full output tuple to coordinates in J. Therefore adequacy of one subfamily would imply adequacy of the full family, contradicting the premise.

The quantifier ranges over every subset of the index type, so finite, countable, and full selections are all included without separate cardinality assumptions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyInadequacyPersistence.full_family_inadequacy_persists_to_subfamilies`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/LatentAdequacyCriterion](../DefinitionEscape/LatentAdequacyCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
