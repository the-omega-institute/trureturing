# Conditional factorization and shared ancestors

## Abstract

Complete responses factorize under coordinatewise independent-source evaluation. Sharing a random ancestor changes that premise, even when every equation has independent local noise.

Verification status is recorded in the unified causal partial-identification research ledger. The authored proof source is not itself evidence that the protected Lean build or maximal-catalog seal has passed.

**Theorem 1.1 (Average the conditional products).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.conditional_joint_benefit_eq_weighted_products`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.conditional_joint_benefit_eq_weighted_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditional independence gives the weighted average of stratum-specific benefit products. It does not by itself give a product of population averages.

**Theorem 1.2 (Exact binary covariance certificate).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.binary_mixture_covariance_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.binary_mixture_covariance_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference between the two aggregation formulas is a rational polynomial equal to the stratum-weight product times the two conditional rate differences.

**Theorem 1.3 (Exact criterion for two positive strata).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.binary_mixture_factorizes_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.binary_mixture_factorizes_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two positive-probability strata, the population product formula holds exactly when at least one conditional mechanism benefit rate is constant.

**Theorem 1.4 (Evaluate the explicit shared-root response law).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.sharedRootJointLaw_mass`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.sharedRootJointLaw_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fair root and two independent degenerate local disturbances push forward to equal mass on two diagonal complete-response states.

**Theorem 1.5 (Independent local noise permits dependent benefit events).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.independent_local_noise_shared_root_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.independent_local_noise_shared_root_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both mechanism benefit rates and their intersection equal one half in the shared-root model, whereas their marginal product equals one quarter.

**Theorem 1.6 (Expose the failed componentwise-map premise).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.shared_root_responses_do_not_factorize`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.shared_root_responses_do_not_factorize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The resulting complete response law is not a product law. The existing product-pushforward theorem remains valid because its coordinatewise-map premise does not hold for this construction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.binary_mixture_covariance_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.binary_mixture_factorizes_iff`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.conditional_joint_benefit_eq_weighted_products`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.independent_local_noise_shared_root_counterexample`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.sharedRootJointLaw_mass`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.shared_root_responses_do_not_factorize`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/MarkovianJointBenefitMarginalSharpBounds](../CausalMoments/MarkovianJointBenefitMarginalSharpBounds.md)
