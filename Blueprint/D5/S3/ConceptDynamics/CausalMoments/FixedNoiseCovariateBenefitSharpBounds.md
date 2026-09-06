# Exact sharp interval with one fixed-noise model

## Abstract

The lower and upper endpoints are weighted products of the local benefit endpoints. Rational interpolation selects target values, local sharpness constructs response laws, and full tables realize every stratum simultaneously. Necessity covers arbitrary cross-row dependence.

**Definition 1.1 (Treatment evaluation of a fixed response table).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseOutcome`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseOutcome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Control and treatment select different coordinates of the same row of the same exogenous table.

**Theorem 1.2 (Complete response-pair identity).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseOutcome_response`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseOutcome_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two potential outcomes reproduce the selected table row exactly.

**Definition 1.3 (Actual row marginals in a common model).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseStratumModel`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseStratumModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing independent-mechanism response carrier is populated using the marginals of the two full-table laws.

**Definition 1.4 (Four conditional intervention marginals).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.HasConditionalFourMarginals`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.HasConditionalFourMarginals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The model fixes both treatment success probabilities for both mechanisms in each stratum. Values in null strata are kernel specifications.

**Definition 1.5 (Population benefit from the actual source law).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseJointBenefit`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseJointBenefit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the simultaneous-benefit cells of the common covariate and two-table pushforward law.

**Theorem 1.6 (Weighted stratum product formula).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseJointBenefit_eq_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseJointBenefit_eq_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The population query equals the weighted sum of joint-benefit probabilities of the actual stratum response laws.

**Theorem 1.7 (Discharge simultaneous stratum selection).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseStrata_simultaneously_realized`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseStrata_simultaneously_realized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An explicit pair of full-table disturbances realizes any finite family of independent-mechanism stratum laws.

**Theorem 1.8 (Exact sharp interval with one fixed-noise model).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoise_covariate_joint_benefit_sharp_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoise_covariate_joint_benefit_sharp_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower and upper endpoints are weighted products of the local benefit endpoints. Rational interpolation selects target values, local sharpness constructs response laws, and full tables realize every stratum simultaneously. Necessity covers arbitrary cross-row dependence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.HasConditionalFourMarginals`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseJointBenefit`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseJointBenefit_eq_weighted`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseOutcome`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseOutcome_response`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseStrata_simultaneously_realized`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoiseStratumModel`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds.fixedNoise_covariate_joint_benefit_sharp_iff`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable](FiniteConditionalResponseTable.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds](MarkovianJointBenefitMarginalSharpBounds.md)
