# Markovian Response-Law Factorization

## Abstract

Independent finite exogenous components induce product-factorized response laws, while counterfactual event probabilities become exact linear objectives after all but one component law are fixed.

The Markovian assumption is placed at the exogenous-response level. Two normalized local response laws combine by a product mass, and coordinatewise deterministic response maps preserve that product factorization under finite pushforward.

A component may represent one Markovian disturbance or an entire quasi-Markovian confounded component. Dependence inside a component remains unrestricted. Independence is asserted only across the displayed components.

A Boolean counterfactual event is generally bilinear in two unknown component laws. Once the right component law is fixed, summing its event-weighted mass produces one rational coefficient for each left response state. The remaining optimization is therefore an ordinary finite linear program with exact primal-dual certificates.

The global product-law family is nonconvex. Mixtures of two Markovian response laws may introduce dependence between component responses, so endpoint witnesses cannot be interpolated without an additional inner-family construction.

**Theorem 1.1 (Componentwise deterministic pushforward preserves product factorization).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.product_pushforward_factorizes`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.product_pushforward_factorizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pushing an independent product exogenous law through two coordinatewise response maps gives exactly the product of the two local response pushforwards. Every coefficient is checked by finite sum rearrangement.

**Theorem 1.2 (Independent exogenous components induce a Markovian response law).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.independent_exogenous_components_induce_markovian_response_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.independent_exogenous_components_induce_markovian_response_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalized local exogenous laws are pushed to normalized local response laws, and the preceding factorization identity packages the resulting joint response distribution as Markovian at the selected component resolution.

**Theorem 1.3 (Fixing one component converts a counterfactual event to a linear objective).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.responseEventMass_product_eq_left_linearObjective`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.responseEventMass_product_eq_left_linearObjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of a left response state is the right-law probability of all right responses that jointly satisfy the event. The full product-law event probability is exactly the resulting rational linear objective.

**Theorem 1.4 (Fixed-component LP certificates bound the Markovian event probability).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.response_event_bounds_of_fixed_right_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.response_event_bounds_of_fixed_right_certificates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact rational lower and upper dual certificates for the remaining component law replay directly as bounds on the original counterfactual event probability.

**Theorem 1.5 (The Markovian response-law family is globally nonconvex).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.markovian_response_laws_not_closed_under_midpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.markovian_response_laws_not_closed_under_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two degenerate product response laws are constructed. Their midpoint places equal mass on the two diagonal Boolean states and violates the product determinant identity, giving an exact obstruction to convex interpolation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.independent_exogenous_components_induce_markovian_response_law`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.markovian_response_laws_not_closed_under_midpoint`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.product_pushforward_factorizes`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.responseEventMass_product_eq_left_linearObjective`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization.response_event_bounds_of_fixed_right_certificates`
- Dependency: [D5/S0/Certificates/LinearObjectiveDual](../../../S0/Certificates/LinearObjectiveDual.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature](CanonicalResponseSignature.md)
