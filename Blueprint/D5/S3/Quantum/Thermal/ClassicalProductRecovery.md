# Explicit Classical Product Recovery

## Abstract

For probability measures and a Markov kernel, the product reference law splits the joint Kullback–Leibler divergence into a marginal term and a hidden conditional defect. The explicitly constructed product lift attains the minimum, and reversible measure-preserving observation squares conserve both full and observed divergences.

**Theorem 1.1 (Product recovery chain).**

For probability measures `ν`, `γr`, and `γh`, and a Markov kernel `κ`,

$$\operatorname{KL}(ν \otimes κ\,\|\,γr \times γh)=\operatorname{KL}(ν\,\|\,γr)+\operatorname{KL}(ν \otimes κ\,\|\,ν \times γh).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.product_recovery_chain` (`✓ std3`). ∎

**Theorem 1.2 (Finite recovery terms).**

If the total divergence in Theorem 1.1 is finite, both summands are finite.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_terms_finite` (`✓ std3`). ∎

**Theorem 1.3 (Real recovery defect).**

Under the finiteness hypothesis, subtracting the marginal divergence from the total divergence gives the real conditional defect.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.recovery_defect_real` (`✓ std3`). ∎

**Theorem 1.4 (Explicit product minimum).**

The product lift `ν × γh` has divergence `KL(ν‖γr)` and is no larger than the divergence of any Markov-disintegrated joint law with first marginal `ν`.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_minimizes` (`✓ std3`). ∎

**Theorem 1.5 (Unique product minimum under finite marginal divergence).**

If `KL(ν‖γr)` is finite, equality in the minimum holds exactly when the joint law is the product lift.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.thermalLift_unique_minimum` (`✓ std3`). ∎

**Theorem 1.6 (Reversible KL invariance).**

Measurable equivalences preserve the KL divergence of finite measures. A reference-preserving equivalence therefore preserves the divergence after pushing forward the first measure.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.klDiv_measurableEquiv` and `D5/S3/Quantum/Thermal/ClassicalProductRecovery.klDiv_reference_preserving` (`✓ std3`). ∎

**Theorem 1.7 (Predictive defect invariance).**

When an observation intertwines two measurable equivalences and both reference measures are preserved, the pair consisting of full and observed KL divergences is invariant.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/ClassicalProductRecovery.predictive_defect_invariant` (`✓ std3`). ∎

## References

- Truth anchors: the declarations listed in the theorem statements above.
