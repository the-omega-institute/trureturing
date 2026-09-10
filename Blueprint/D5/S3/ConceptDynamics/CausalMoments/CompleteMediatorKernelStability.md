# CompleteMediatorKernelStability

## Abstract

Finite rational nonfair outcome transport on the original complete-mediation model.

All theorem entries are bound to their Lean declarations without formula projection. The original mediator and outcome probability-law semantics are retained. No compilation or independent review status is asserted by this source document.

**Definition 1.1 (Keep the signed directed contribution).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelDrift`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelDrift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The drift is half the sum of treated-minus-control mediator mass times the target-minus-source outcome mean.

**Definition 1.2 (Exclude forced self-pair mass).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.sensitivityWeight`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.sensitivityWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is one minus the absolute value of combined mediator mass minus one. It is the maximal singleton cut allowed by the original marginals.

**Definition 1.3 (Uniform off-diagonal sensitivity radius).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelRadius`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Half the weighted sum of absolute coordinate changes bounds the centered objective change for every compatible mediator coupling.

**Theorem 1.4 (Reverse the signed drift).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelDrift_swap`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelDrift_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging source and target reverses the drift sign.

**Theorem 1.5 (Symmetric transport radius).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelRadius_swap`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelRadius_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging source and target leaves the radius unchanged.

**Theorem 1.6 (Original causal cut identity with original means).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.completeMediatorBenefit_mean_identity`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.completeMediatorBenefit_mean_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual benefit equals half the expected cut plus half the mean drift determined by the original mediator marginals. No fairness premise is used.

**Theorem 1.7 (One construction controls the entire coupling family).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.exists_uniform_kernel_transport`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.exists_uniform_kernel_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The moved outcome law is chosen before quantifying over mediator couplings. It has the prescribed target means and obeys the drift-corrected bound for every original coupling with the nominated marginals.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.completeMediatorBenefit_mean_identity`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.exists_uniform_kernel_transport`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelDrift`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelDrift_swap`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelRadius`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.kernelRadius_swap`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.sensitivityWeight`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport](BooleanOutcomeMarginalTransport.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation](UnknownCouplingFairMediation.md)
