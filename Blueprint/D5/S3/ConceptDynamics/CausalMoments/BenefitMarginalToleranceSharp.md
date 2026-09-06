# Sharp Boolean benefit ambiguity under marginal tolerances

## Abstract

For every nonnegative rational tolerance pair, explicit causal response laws attain the largest possible benefit discrepancy, with a matching least residual certificate.

The array carrier is Fin 4 in response order 00,01,10,11; the two feature columns are indexed by Fin 2. All scalar entries and tolerances are rational. In the final theorem high and low are existing FiniteResponseLaw values on Bool times Bool, and all causal readouts are the existing source functions.

**Definition 1.1 (Actual potential-outcome indicator columns).**

$$(\operatorname{benefitMomentFeature}) = ([[0, 0], [0, 1], [1, 0], [1, 1]])$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitMomentFeature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two columns encode control and treated success. The proof identifies their indexed expectations with controlSuccessMarginal and treatmentSuccessMarginal.

**Definition 1.2 (Benefit indicator).**

$$(\operatorname{benefitMomentQuery}) = ([0, 1, 0, 0])$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitMomentQuery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This selects response 01 and is identified with benefitResponseMass on the original response-law carrier.

**Definition 1.3 (Closed ambiguity formula).**

$$\forall eta0, eta1, (\operatorname{benefitAmbiguityValue}(eta0, eta1)) = (\operatorname{min}(1, \frac{((1) + (eta0)) + (eta1)}{2}))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitAmbiguityValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameters bound differences between two models. They are not radii of confidence intervals about a fixed observation.

**Definition 1.4 (Raw two-regime certificate).**

$$\forall eta0, eta1, (\operatorname{benefitToleranceCertificate}(eta0, eta1)) = (\operatorname{ite}(((eta0) + (eta1)) \le (1), \{(high) = ([0, \frac{((1) + (eta0)) + (eta1)}{2}, (1) - (\frac{((1) + (eta0)) + (eta1)}{2}), 0]), (low) = ([(1) - (\frac{((1) + (eta0)) - (eta1)}{2}), 0, 0, \frac{((1) + (eta0)) - (eta1)}{2}]), (envelope) = (\{(offset) = (0), (coefficient) = ([-\frac{1}{2}, \frac{1}{2}]), (lower) = (0), (upper) = (\frac{1}{2})\})\}, \{(high) = ([0, 1, 0, 0]), (low) = ([(1) - (\operatorname{min}(1, eta0)), 0, 0, \operatorname{min}(1, eta0)]), (envelope) = (\{(offset) = (0), (coefficient) = ([0, 0]), (lower) = (0), (upper) = (1)\})\}))$$

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitToleranceCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each record displays the high and low four-cell laws plus every envelope field. The first branch includes total tolerance one; the second saturates the probability range. No certificate validity or optimality fact is stored as a field.

**Theorem 1.5 (Acceptance for all nonnegative tolerances).**

$$\forall eta0, eta1, (((0) \le (eta0)) \land ((0) \le (eta1))) \Rightarrow ((\operatorname{checkContactCertificate}(\operatorname{benefitMomentFeature}, \operatorname{benefitMomentQuery}, (\lambda j \mapsto \operatorname{ite}((j) = (0), eta0, eta1)), \operatorname{benefitToleranceCertificate}(eta0, eta1))) = (true))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitToleranceCertificate_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both parameter regimes are checked symbolically, including zeros, the boundary and tolerances larger than one. No optimizer or bounded sample set is assumed.

**Theorem 1.6 (Exact value of the certificate).**

$$\forall eta0, eta1, (\operatorname{residualBudget}((\lambda j \mapsto \operatorname{ite}((j) = (0), eta0, eta1)), \operatorname{envelope}(\operatorname{benefitToleranceCertificate}(eta0, eta1)))) = (\operatorname{benefitAmbiguityValue}(eta0, eta1))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitToleranceCertificate_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This algebraic equality holds for all rational parameters. Nonnegativity is needed separately for acceptance and the sharpness theorem.

**Theorem 1.7 (Universal bound, attaining causal pair and least dual value).**

$$\forall eta0, eta1, (((0) \le (eta0)) \land ((0) \le (eta1))) \Rightarrow ((\forall high, low, (((\lvert(\operatorname{controlSuccessMarginal}(\operatorname{mass}(high))) - (\operatorname{controlSuccessMarginal}(\operatorname{mass}(low)))\rvert) \le (eta0)) \land ((\lvert(\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(high))) - (\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(low)))\rvert) \le (eta1))) \Rightarrow ((\lvert(\operatorname{benefitResponseMass}(\operatorname{mass}(high))) - (\operatorname{benefitResponseMass}(\operatorname{mass}(low)))\rvert) \le (\operatorname{benefitAmbiguityValue}(eta0, eta1)))) \land (\exists high, low, (((\lvert(\operatorname{controlSuccessMarginal}(\operatorname{mass}(high))) - (\operatorname{controlSuccessMarginal}(\operatorname{mass}(low)))\rvert) \le (eta0)) \land ((\lvert(\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(high))) - (\operatorname{treatmentSuccessMarginal}(\operatorname{mass}(low)))\rvert) \le (eta1))) \land (((\operatorname{benefitResponseMass}(\operatorname{mass}(high))) - (\operatorname{benefitResponseMass}(\operatorname{mass}(low)))) = (\operatorname{benefitAmbiguityValue}(eta0, eta1)))) \land (\operatorname{IsLeast}(\operatorname{residualBudgetValues}(\operatorname{benefitMomentFeature}, \operatorname{benefitMomentQuery}, (\lambda j \mapsto \operatorname{ite}((j) = (0), eta0, eta1))), \operatorname{benefitAmbiguityValue}(eta0, eta1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefit_marginal_tolerance_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first clause bounds every original-carrier pair. The second constructs normalized nonnegative original response laws attaining the oriented difference. The third certifies the least residual budget on the same four allowed cells. This is a global pairwise modulus over all marginal locations, not the identified interval at one fixed observed marginal vector.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitAmbiguityValue`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitMomentFeature`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitMomentQuery`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitToleranceCertificate`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitToleranceCertificate_accepted`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefitToleranceCertificate_budget`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/BenefitMarginalToleranceSharp.benefit_marginal_tolerance_sharp`
- Dependency: [D5/S0/Certificates/RationalMomentAmbiguityCertificate](../../../S0/Certificates/RationalMomentAmbiguityCertificate.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary](../PartialIdentification/MarkovianBenefitIdentificationBoundary.md)
