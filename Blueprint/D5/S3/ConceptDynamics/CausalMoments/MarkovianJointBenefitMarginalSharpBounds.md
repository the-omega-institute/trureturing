# Joint benefit from four interventional marginals

## Abstract

Four single-world marginals leave two internal response couplings unknown. The joint-benefit query ranges over the product of the two local sharp intervals under complete-mechanism independence.

Verification status is recorded in the unified causal partial-identification research ledger. The authored proof source is not itself evidence that the protected Lean build or maximal-catalog seal has passed.

**Theorem 1.1 (Rational products fill the endpoint product interval).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.nonnegative_product_interval_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.nonnegative_product_interval_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A two-edge path in a nonnegative parameter rectangle realizes every rational target using rational factors. It does not mix two product laws.

**Theorem 1.2 (Recover the local benefit interval).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.outcomeLaw_benefit_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.outcomeLaw_benefit_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local interval follows from the existing assignment-outcome sharpness theorem, avoiding a second four-cell necessity proof.

**Theorem 1.3 (Exact range with all four intervention marginals fixed).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.four_marginal_joint_benefit_sharp_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.four_marginal_joint_benefit_sharp_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem constructs complete response laws for every rational target between the products of the local lower and upper benefit endpoints.

**Theorem 1.4 (Balanced intervention marginals leave an interval).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.balanced_four_marginal_sharp_interval`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.balanced_four_marginal_sharp_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When all four success marginals equal one half, every target from zero to one quarter is attained by independent complete mechanisms.

**Theorem 1.5 (A full-model observation-kernel witness).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.joint_benefit_strictly_refines_four_marginal_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.joint_benefit_strictly_refines_four_marginal_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two models on the existing full rational model carrier have identical four-marginal readouts and different joint-benefit values. No finite test arena or escape-rate score is introduced.

**Theorem 1.6 (No reconstruction from the four marginal readout).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.no_joint_benefit_reconstruction_from_four_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.no_joint_benefit_reconstruction_from_four_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness rules out every function that would reconstruct joint benefit from four intervention marginals on all models in this family.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.balanced_four_marginal_sharp_interval`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.four_marginal_joint_benefit_sharp_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.joint_benefit_strictly_refines_four_marginal_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.no_joint_benefit_reconstruction_from_four_marginals`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.nonnegative_product_interval_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds.outcomeLaw_benefit_bounds`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds](MarkovianJointMechanismBenefitSharpBounds.md)
