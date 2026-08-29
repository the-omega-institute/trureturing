# Scientific Gain Does Not Identify Generalization

## Abstract

A finite scientific-gain witness can have opposite conditional future loss signs.

**Theorem 1.1 (Equal observed marginals admit opposite future loss signs).**

$$\exists P \in \operatorname{Unit}\left(\right) \times \operatorname{Bool}\left(\right) \to \operatorname{Real}\left(\right), Q \in \operatorname{Unit}\left(\right) \times \operatorname{Bool}\left(\right) \to \operatorname{Real}\left(\right), nextEvidence \in \operatorname{Bool}\left(\right) \to \operatorname{Bool}\left(\right), lastEvidence \in \operatorname{Unit}\left(\right) \to \operatorname{Bool}\left(\right), evaluate \in \operatorname{Unit}\left(\right) \to \left(\operatorname{Bool}\left(\right) \to \left(\operatorname{Bool}\left(\right) \to \operatorname{Real}\left(\right)\right)\right), K \in \operatorname{WitnessCommitment}\left(\right), hStar \in \operatorname{Unit}\left(\right), zStar \in \operatorname{Bool}\left(\right), a \in \operatorname{Bool}\left(\right), b \in \operatorname{Bool}\left(\right),\; \operatorname{IsFiniteJointLaw}\left(P\right) \land \left(\operatorname{IsFiniteJointLaw}\left(Q\right) \land \left(\left(\forall h \in \operatorname{Unit}\left(\right),\; \operatorname{marginal}\left(P, h\right) = \operatorname{marginal}\left(Q, h\right)\right) \land \left(\operatorname{marginal}\left(P, hStar\right) = \operatorname{marginal}\left(Q, hStar\right) \land \left(0 < \operatorname{marginal}\left(P, hStar\right) \land \left(lastEvidence\left(hStar\right) = zStar \land \left(\operatorname{ScientificGain}\left(evaluate, K, zStar, a, b\right) \land \left(\left(\forall action \in \operatorname{Bool}\left(\right),\; \operatorname{AbsolutelyIntegrableLoss}\left(P, evaluate, \operatorname{comparator}\left(K\right), nextEvidence, action\right) \land \operatorname{AbsolutelyIntegrableLoss}\left(Q, evaluate, \operatorname{comparator}\left(K\right), nextEvidence, action\right)\right) \land \left(\operatorname{conditionalExpectedLossDifference}\left(P, hStar, evaluate, \operatorname{comparator}\left(K\right), nextEvidence, a, b\right) < 0 \land 0 < \operatorname{conditionalExpectedLossDifference}\left(Q, hStar, evaluate, \operatorname{comparator}\left(K\right), nextEvidence, a, b\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeLaws/ScientificGainGeneralizationReversal.scientific_gain_generalization_sign_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two explicitly normalized Unit-by-Bool joint laws have values in the unit interval and the same complete observed marginal. Their common history has positive mass, and its designated last record is the one used by ScientificGain.

Both actions' losses are explicitly absolutely summable under both finite laws. The loss and its difference use the same evaluator, frozen commitment comparator, and total next-evidence map as ScientificGain.

Conditioning the first law puts all future mass on the record where the committed action wins, giving loss difference minus one. Conditioning the second puts all mass on the record where the ranking reverses, giving plus one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeLaws/ScientificGainGeneralizationReversal.scientific_gain_generalization_sign_reversal`
- Dependency: [D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion](../Governance/TargetLaunderingCriterion.md)
- Dependency: [D5/S3/Divergence/ChainRule](../../Divergence/ChainRule.md)
