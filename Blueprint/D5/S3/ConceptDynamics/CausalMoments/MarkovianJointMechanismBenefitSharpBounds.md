# Sharp Joint-Benefit Bounds Across Markovian Mechanisms

## Abstract

Two mechanism-level benefit events have the full Frechet coupling interval without cross-mechanism restrictions, while independent Markovian outcome mechanisms collapse simultaneous benefit to the product of the two benefit marginals.

Each outcome mechanism stores its own complete pair of control and treated potential outcomes. Dependence inside either mechanism remains unrestricted. Markovianity is imposed only between the two complete mechanism response laws.

Projecting a complete response pair to its Boolean benefit status is deterministic. The product-pushforward theorem therefore shows that independent mechanism response laws induce independent benefit indicators.

Without the product restriction, two benefit indicators with marginals b1 and b2 have the exact Frechet range from max of zero and b1 plus b2 minus one, to min of b1 and b2. Under independent mechanisms, simultaneous benefit is exactly b1 times b2.

**Theorem 1.1 (Unrestricted simultaneous benefit has the exact Frechet interval).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.unrestricted_joint_benefit_target_feasible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.unrestricted_joint_benefit_target_feasible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every target in the two-event Frechet interval is attained by an explicit normalized four-cell coupling of the two mechanism-level benefit indicators. Conversely, normalization and cell nonnegativity recover both endpoint inequalities.

**Theorem 1.2 (Benefit-status projection preserves Markovian product structure).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.markovian_benefit_status_pushforward_factorizes`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.markovian_benefit_status_pushforward_factorizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pushing two independent complete outcome-mechanism response laws through their componentwise benefit indicators yields the product of the two marginal benefit-status laws. Internal potential-outcome dependence inside each mechanism is left unchanged before projection.

**Theorem 1.3 (Independent mechanisms point identify simultaneous benefit).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.markovian_joint_benefit_sharp_singleton_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.markovian_joint_benefit_sharp_singleton_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target is realized by two independent complete outcome mechanisms with nominated marginal benefit probabilities exactly when the target equals their product. Explicit component laws provide the attaining structural witness.

**Theorem 1.4 (The half-marginal interval strictly collapses to one quarter).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.half_joint_benefit_strict_tightening`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.half_joint_benefit_strict_tightening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both mechanism benefit probabilities are one half, unrestricted cross-mechanism coupling admits simultaneous benefit zero and every value through one half. Every Markovian two-mechanism model instead has simultaneous benefit exactly one quarter.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.half_joint_benefit_strict_tightening`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.markovian_benefit_status_pushforward_factorizes`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.markovian_joint_benefit_sharp_singleton_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/MarkovianJointMechanismBenefitSharpBounds.unrestricted_joint_benefit_target_feasible_iff`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianBenefitIdentificationBoundary](../PartialIdentification/MarkovianBenefitIdentificationBoundary.md)
