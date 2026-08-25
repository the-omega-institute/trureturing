# Intervention-Family Kernel Monotonicity

## Abstract

Enlarging an arbitrary intervention family shrinks its joint-law equality kernel.

**Theorem 1.1 (More interventions can only shrink the causal residual).**

$$\forall I, M, L: \operatorname{Type},\\{}law: I \to M \to L, A, B: \operatorname{Set}(I),\\{}A \subseteq B\\{}\Rightarrow \operatorname{ker}(\operatorname{jointReadout}(\operatorname{restrict}(law, B))) \subseteq \operatorname{ker}(\operatorname{jointReadout}(\operatorname{restrict}(law, A))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/InterventionFamilyKernelMonotonicity.intervention_family_kernel_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each intervention supplies a law-valued readout on the common model carrier. For any allowed family, the canonical joint readout constructs its complete interventional law profile.

When family A is contained in family B, restricting a B-profile to A recovers the A-profile coordinate by coordinate. Equality of two B-profiles therefore implies equality of their A-profiles.

The public theorem quantifies arbitrary set-indexed families. The existing finite-index theorem is a genuine special case and is not used as coverage for this unrestricted source claim.

Repository and pinned-library searches found no arbitrary-family theorem. The proof evaluates equality of the larger canonical joint readout at each included intervention.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/InterventionFamilyKernelMonotonicity.intervention_family_kernel_monotonicity`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
