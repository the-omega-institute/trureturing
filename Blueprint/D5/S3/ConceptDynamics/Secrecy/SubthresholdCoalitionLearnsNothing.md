# Subthreshold Coalitions Learn Nothing

## Abstract

Structural zero leakage makes every coalition-determined secret function constant, while ignorance of the whole secret alone does not imply zero information.

**Theorem 1.1 (Structural zero leakage makes secret functions constant).**

$$\forall X \in Type, C \in Type, S \in Type, M \in Type, Y \in Type, coalition \in X \to C, secret \in X \to S, common \in X \to M, target \in X \to Y, secretFunction \in S \to Y,\; \left(\operatorname{Nonempty}\left(X\right) \land \left(\operatorname{IsConceptMeet}\left(coalition, secret, common\right) \land \left(\operatorname{ConceptEquivalent}\left(common, \operatorname{constantConcept}\left(X\right)\right) \land \left(target = secretFunction \circ secret \land \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(target\right), coalition\right)\right)\right)\right)\right) \Rightarrow \left(\forall x \in X, y \in X,\; target\left(x\right) = target\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Secrecy/SubthresholdCoalitionLearnsNothing.subthreshold_coalition_learns_nothing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common readout is the meet of the coalition and secret readouts, and structural zero leakage identifies that meet with the constant concept.

Because the target is a function of the secret, its canonical target-image readout factors through the secret. The coalition hypothesis makes it factor through the coalition as well. The meet property therefore makes it factor through the common readout, and hence through the constant concept. Thus every two states have the same target value.

**Lemma 1.2 (Whole-secret ignorance does not imply zero information).**

$$\left(\neg \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(id\right), fst\right)\right) \land \left(\exists target \in Bool \times Bool \to Bool, secretFunction \in Bool \times Bool \to Bool,\; target = secretFunction \circ id \land \left(\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(target\right), fst\right) \land \left(\exists x \in Bool \times Bool, y \in Bool \times Bool,\; target\left(x\right) \ne target\left(y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Secrecy/SubthresholdCoalitionLearnsNothing.ignorance_does_not_imply_zero_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a two-bit secret, let the secret readout be the identity and let the coalition see only the first bit. The coalition cannot recover the whole pair because it loses the second bit. Nevertheless, the first bit is a nonconstant function of the secret and factors through the coalition readout. Failure of full-secret recovery is therefore strictly weaker than learning no secret information.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Secrecy/SubthresholdCoalitionLearnsNothing.ignorance_does_not_imply_zero_information`
- Truth anchor: `D5/S3/ConceptDynamics/Secrecy/SubthresholdCoalitionLearnsNothing.subthreshold_coalition_learns_nothing`
- Dependency: [D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak](../Disclosure/ExactTargetForcedLeak.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
