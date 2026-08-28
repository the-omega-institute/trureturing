# Static and Adaptive Submodularity Separation

## Abstract

A rare posterior branch separates expected from pathwise diminishing returns.

**Theorem 1.1 (Adaptive submodularity implies static submodularity).**

$$\forall mu, A, gPrior, gPath,\\{}\operatorname{AdaptiveSubmodular}\left(mu, A, gPrior, gPath\right) \Rightarrow \operatorname{StaticSubmodular}\left(mu, A, gPrior, gPath\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.adaptive_submodular_implies_static_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive-mass pathwise bound can be multiplied by its mass and summed. Zero-mass outputs contribute zero, and normalization gives the static expected bound.

**Theorem 1.2 (The prior and gate law are normalized).**

$$\operatorname{ProbabilityMass}\left(rarePriorMass\right) \land\\{}\operatorname{ProbabilityMass}\left(rareGateOutcomeMass\right) \land\\{}\operatorname{rareGateOutcomeMass}\left(false\right) = \frac{1}{10}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_prior_and_gate_are_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common state has mass 9/10 and the two rare states each have mass 1/20. The gate's rare output therefore has total mass 1/10.

**Theorem 1.3 (A rare output activates the specialist).**

$$\operatorname{posteriorAfterReadout}\left(gateExperiment, false, none\right) = 0 \land\\{}\operatorname{posteriorAfterReadout}\left(gateExperiment, false, \operatorname{some}\left(false\right)\right) = \frac{1}{2} \land\\{}\operatorname{posteriorAfterReadout}\left(gateExperiment, false, \operatorname{some}\left(true\right)\right) = \frac{1}{2} \land\\{}\operatorname{rarePriorMarginalGain}\left(specialistExperiment\right) = \frac{1}{20} \land\\{}\operatorname{rarePathMarginalGain}\left(false, specialistExperiment\right) = \frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_output_posterior_activates_specialist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditioning on the rare gate output removes the common state. The two remaining states become equiprobable, so specialist value rises from 1/20 to 1/2.

**Theorem 1.4 (The rare-branch instance is statically submodular).**

$$\operatorname{StaticSubmodular}\left(rareGateOutcomeMass, availableAfterGate, rarePriorMarginalGain, rarePathMarginalGain\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_branch_static_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The specialist has gain zero on the common output and gain 1/2 on the rare output. Its expected posterior gain is exactly 1/20, equal to its prior gain.

**Theorem 1.5 (The rare-branch instance is not adaptively submodular).**

$$\neg\operatorname{AdaptiveSubmodular}\left(rareGateOutcomeMass, availableAfterGate, rarePriorMarginalGain, rarePathMarginalGain\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_branch_not_adaptive_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rare output has positive probability, yet its realized specialist gain 1/2 exceeds the prior gain 1/20. This violates the pathwise bound.

**Theorem 1.6 (FPOD principle 246.1).**

$$\neg{\operatorname{StaticSubmodular}\left(rareGateOutcomeMass, availableAfterGate, rarePriorMarginalGain, rarePathMarginalGain\right) \Rightarrow \operatorname{AdaptiveSubmodular}\left(rareGateOutcomeMass, availableAfterGate, rarePriorMarginalGain, rarePathMarginalGain\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.fpod_principle_246_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same finite instance satisfies expected diminishing returns and fails pathwise diminishing returns. Static submodularity therefore does not imply adaptive submodularity.

**Theorem 1.7 (An empty experiment family satisfies both properties).**

$$\operatorname{StaticSubmodular}\left(rareGateOutcomeMass, \operatorname{unavailable}\left(Empty\right), emptyPriorGain, emptyPathGain\right) \land\\{}\operatorname{AdaptiveSubmodular}\left(rareGateOutcomeMass, \operatorname{unavailable}\left(Empty\right), emptyPriorGain, emptyPathGain\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.empty_experiment_family_satisfies_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With no next experiment, both marginal-return conditions are vacuous. Only normalization of the gate-output law remains.

**Theorem 1.8 (An unavailable singleton family satisfies both properties).**

$$\operatorname{StaticSubmodular}\left(rareGateOutcomeMass, \operatorname{unavailable}\left(Unit\right), zeroGain, zeroGain\right) \land\\{}\operatorname{AdaptiveSubmodular}\left(rareGateOutcomeMass, \operatorname{unavailable}\left(Unit\right), zeroGain, zeroGain\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.singleton_experiment_family_satisfies_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton experiment family whose sole member is unavailable has no next-step obligation, so both conditions again hold vacuously.

**Theorem 1.9 (Constant zero gain satisfies both properties).**

$$\operatorname{StaticSubmodular}\left(rareGateOutcomeMass, allExperiments, zeroGain, zeroGain\right) \land\\{}\operatorname{AdaptiveSubmodular}\left(rareGateOutcomeMass, allExperiments, zeroGain, zeroGain\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.constant_gain_satisfies_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every prior and posterior marginal gain is zero, all expected and pathwise comparisons reduce to equality.

**Theorem 1.10 (Posterior-independent gain satisfies both properties).**

$$\operatorname{StaticSubmodular}\left(rareGateOutcomeMass, availableAfterGate, rarePriorMarginalGain, \operatorname{posteriorIndependent}\left(rarePriorMarginalGain\right)\right) \land\\{}\operatorname{AdaptiveSubmodular}\left(rareGateOutcomeMass, availableAfterGate, rarePriorMarginalGain, \operatorname{posteriorIndependent}\left(rarePriorMarginalGain\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.posterior_not_updating_satisfies_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every posterior marginal equals its prior marginal, conditioning cannot create a pathwise increase and both notions reduce to equality.

## References

- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.adaptive_submodular_implies_static_submodular`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.constant_gain_satisfies_both`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.empty_experiment_family_satisfies_both`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.fpod_principle_246_1`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.posterior_not_updating_satisfies_both`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_branch_not_adaptive_submodular`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_branch_static_submodular`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_output_posterior_activates_specialist`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.rare_prior_and_gate_are_normalized`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation.singleton_experiment_family_satisfies_both`
