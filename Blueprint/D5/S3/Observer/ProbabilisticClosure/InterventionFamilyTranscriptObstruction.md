# Intervention-Family Transcript Obstruction

## Abstract

Repeated sampling and adaptive or randomized processing cannot separate two models that have the same law under every intervention in the allowed family.

**Theorem 1.1 (Repeated use of one intervention family cannot cross its kernel).**

$$\forall Intervention \in Type, Model \in Type, Law \in Type, TranscriptLaw \in Type, DecisionLaw \in Type, law \in Intervention \to \left(Model \to Law\right), target \in Model \to DecisionLaw, M \in Model, N \in Model, adaptiveTranscriptLaw \in Nat \to \left(Nat \to \left(Model \to TranscriptLaw\right)\right),\; \left(target\left(M\right) \ne target\left(N\right) \land \left(\operatorname{jointReadout}\left(law, M\right) = \operatorname{jointReadout}\left(law, N\right) \land \left(\forall repetitions \in Nat, sampleSize \in Nat, M \in Model, N \in Model,\; \operatorname{jointReadout}\left(law, M\right) = \operatorname{jointReadout}\left(law, N\right) \Rightarrow adaptiveTranscriptLaw\left(repetitions, sampleSize, M\right) = adaptiveTranscriptLaw\left(repetitions, sampleSize, N\right)\right)\right)\right) \Rightarrow \left(\forall repetitions \in Nat, sampleSize \in Nat, randomizedPostprocess \in TranscriptLaw \to DecisionLaw,\; randomizedPostprocess\left(adaptiveTranscriptLaw\left(repetitions, sampleSize, M\right)\right) = randomizedPostprocess\left(adaptiveTranscriptLaw\left(repetitions, sampleSize, N\right)\right) \land \left(\neg \left(randomizedPostprocess\left(adaptiveTranscriptLaw\left(repetitions, sampleSize, M\right)\right) = target\left(M\right) \land randomizedPostprocess\left(adaptiveTranscriptLaw\left(repetitions, sampleSize, N\right)\right) = target\left(N\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/InterventionFamilyTranscriptObstruction.repeated_intervention_family_kernel_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The profile jointReadout(law) is the canonical tuple of all allowed intervention laws. Equality of every family member makes this complete profile equal at the two models.

At the law level, an adaptive transcript constructor may use arbitrary repeat and sample counts, and the final law may undergo arbitrary randomized postprocessing. Both are functions of the same family profile, so their final laws remain equal.

If both final laws were exact, their equality would force the two target values to agree, contradicting the source distinction.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/InterventionFamilyTranscriptObstruction.repeated_intervention_family_kernel_obstruction`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
