# Conditional factorization and shared ancestors

## Abstract

Complete responses factorize under coordinatewise independent-source evaluation. Sharing a random ancestor changes that premise, even when every equation has independent local noise.

Verification status is recorded in the unified causal partial-identification research ledger. The authored proof source is not itself evidence that the protected Lean build or maximal-catalog seal has passed.

For a triangle model, let alpha, beta and gamma range over arbitrary standard Borel spaces with probability laws muAlpha, muBeta and muGamma. Use the source carrier alpha × (beta × gamma) and the law mu = muAlpha.prod (muBeta.prod muGamma). Its three own coordinate marginals are exactly the displayed factors: apply MeasureTheory.Measure.fst_prod and MeasureTheory.Measure.snd_prod at each product level. Thus the product of those own marginals is mu itself, and InformationTheory.klDiv_self gives total correlation D(mu || muAlpha × muBeta × muGamma) = 0. This argument requires neither finite sources nor uniformity, nondegeneracy or strictly positive masses.

The response maps need not preserve source independence. In the stochastic version, Alice has a measurable probability kernel K_A on the incident pair (beta, gamma), Bob has K_B on (gamma, alpha), and Charlie has K_C on (alpha, beta). The observed joint law is the integral, under that same mu, of the product of the three conditional output laws. The source KL conclusion applies to every such choice of kernels; it asserts independence of the sources and imposes no product conclusion on the output law.

To obtain an explicit triangle-local dependent law, take all three edge carriers to be Bool, gamma fair, and alpha and beta concentrated at false. Alice outputs (false, gamma), Bob outputs (false, gamma), and Charlie outputs the constant false. These are deterministic measurable kernels: Alice uses only (beta, gamma), Bob only (gamma, alpha), and Charlie only (alpha, beta). Their joint law gives mass one half to each of (((false, false), (false, false)), false) and (((false, true), (false, true)), false), and zero elsewhere.

The parameter correspondence with the existing shared-root model is exact. Permute the source coordinates by (alpha, (beta, gamma)) ↦ (gamma, (beta, alpha)); the resulting law is sharedRootSourceLaw, whose first coordinate has balancedCovariateLaw and whose two remaining coordinates have boolPointLaw false. The Alice–Bob response pair is sharedRootResponse of this permuted source. Its pushforward is therefore sharedRootJointLaw, and the triple law is that very law with a constant Charlie coordinate appended. The native finite laws use rational singleton masses; casting those masses to Real and then applying ENNReal.ofReal gives the same probability measures and the same deterministic-kernel product law, rather than a separately chosen law with matching marginals.

Under this single observed law, each of the events that Alice or Bob has second output coordinate true has probability one half, and their intersection also has probability one half. A product of their own marginals would give one quarter to that intersection. This is the triangle realization of shared_root_responses_do_not_factorize, with sharedRootJointLaw_mass and independent_local_noise_shared_root_counterexample supplying the native mass identities. The third party is constant, so dependence of the Alice–Bob marginal already prevents independence of all three outputs; no common tripartite source is used.

This construction is an application of the cited existing declarations. It establishes that independent sources allow dependent outputs. Sharing an edge alone does not force dependence: constant responses, or responses that ignore that edge, are allowed. The example does not assert a general realization theorem for arbitrary stochastic kernels, a convexity property of the full triangle image, or a resource or physical-realization claim.

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
