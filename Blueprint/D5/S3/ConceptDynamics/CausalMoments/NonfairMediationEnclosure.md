# NonfairMediationEnclosure

## Abstract

Finite rational nonfair outcome transport on the original complete-mediation model.

All theorem entries are bound to their Lean declarations without formula projection. The original mediator and outcome probability-law semantics are retained. No compilation or independent review status is asserted by this source document.

**Definition 1.1 (Original attainable values at a given kernel).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.kernelBenefitValues`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.kernelBenefitValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both independent mechanism laws range subject to the original mediator marginals, complete-mediation equations and all target outcome means.

**Theorem 1.2 (Propagate a valid global bound).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.transfer_kernel_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.transfer_kernel_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse outcome transports carry any valid source-kernel bound to a bound on the entire target-kernel family.

**Theorem 1.3 (Compare two attained optima).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.attained_kernel_optima_stability`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.attained_kernel_optima_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual greatest-value premises give the signed optimum stability formula. This corollary does not assert general optimizer existence; the principal enclosure below supplies a feasible law unconditionally.

**Theorem 1.4 (The fair anchor is an upper envelope after centering).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.partition_anchor_upper`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.partition_anchor_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an optimal original marginal partition, its half-score plus the exact drift bounds every nonfair model. No positive radius is added on this side.

**Theorem 1.5 (Construct a feasible nonfair model and a global bound).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.nonfair_kernel_global_enclosure`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.nonfair_kernel_global_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing fair partition theorem supplies an anchor and original mediator coupling. Transporting only its outcome disturbance constructs a target-kernel law within one radius of the globally valid upper envelope. No nonfair optimizer is assumed.

**Theorem 1.6 (Nonnegative improved weights).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.sensitivityWeight_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.sensitivityWeight_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The off-diagonal weight lies between zero and the older combined-marginal weight.

**Theorem 1.7 (No dimension multiplier for uniform errors).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.kernelRadius_le_uniform_error`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.kernelRadius_le_uniform_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common coordinate error bound epsilon yields radius at most epsilon, using total combined mediator mass two.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.attained_kernel_optima_stability`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.kernelBenefitValues`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.kernelRadius_le_uniform_error`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.nonfair_kernel_global_enclosure`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.partition_anchor_upper`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.sensitivityWeight_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.transfer_kernel_upper_bound`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability](CompleteMediatorKernelStability.md)
