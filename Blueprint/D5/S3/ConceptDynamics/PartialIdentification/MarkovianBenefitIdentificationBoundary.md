# The Markovian Boundary for Probability of Benefit

## Abstract

Independent treatment-assignment noise leaves Boolean probability of benefit at its exact Frechet interval, while an additional factorization of the two potential-outcome response coordinates point identifies benefit.

A standard Markovian treatment-outcome model separates the treatment-assignment disturbance from the outcome-mechanism disturbance. Both potential outcomes remain coordinates of the same outcome response type, so their cross-world dependence is unrestricted by that separation.

The module constructs an explicit four-cell outcome-response law for every target in the ordinary Boolean benefit interval. Pairing that outcome law with any normalized independent assignment law produces a Markovian assignment-outcome model with the same target. Markovian assignment independence therefore does not shrink the sharp interval.

A second theorem factorizes the two potential-outcome coordinates themselves. This extra cross-world restriction is stronger than standard Markovianity and forces the benefit probability to equal one minus the control success probability, multiplied by the treated success probability.

**Theorem 1.1 (Markovian assignment independence preserves the exact Frechet interval).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.markovian_benefit_target_feasible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.markovian_benefit_target_feasible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A benefit target is realized by a product assignment-outcome response law exactly when it lies between the positive marginal difference and the smaller of treated success and control failure. Necessity uses nonnegativity and normalization. Sufficiency uses an explicit four-cell response law.

**Theorem 1.2 (Equal marginals admit distinct Markovian benefit probabilities).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.markovian_assignment_noise_does_not_point_identify_benefit`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.markovian_assignment_noise_does_not_point_identify_benefit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two Markovian models have control and treated success probabilities one half. One has benefit zero and the other has benefit one half, giving a concrete machine-checked failure of point identification.

**Theorem 1.3 (Cross-world response-coordinate factorization point identifies benefit).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.response_coordinate_factorization_point_identifies_benefit`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.response_coordinate_factorization_point_identifies_benefit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the control and treated potential-outcome coordinates are themselves product-factorized, the benefit cell is exactly the product of control failure and treated success. The theorem makes this additional assumption explicit rather than attributing it to ordinary Markovian SCM semantics.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.markovian_assignment_noise_does_not_point_identify_benefit`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.markovian_benefit_target_feasible_iff`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary.response_coordinate_factorization_point_identifies_benefit`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization](MarkovianResponseLawFactorization.md)
