# Elimination in the normalized hard-core jet

## Abstract

Elimination in the normalized hard-core jet

**Theorem 1.1 (The two slopes permitted by matching coherence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination.fold_slopes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination.fold_slopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the displayed nonzero conditions, solving the regular quadratic equations factors the coherence difference. Vanishing of that difference forces the reference slope one or the second root given by the ratio of the fold coefficients.

**Theorem 1.2 (The residual quartic after eliminating regular rows).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination.quartic_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination.quartic_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the second root, the specified cubic regular-row relation accounts for a reparameterization term. Subtracting its quartic contribution to the forbidden population yields the explicit rational expression in length and the Fibonacci ratio.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination.fold_slopes`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination.quartic_difference`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreQuarticSign](PeriodicMPSUniformHardCoreQuarticSign.md)
