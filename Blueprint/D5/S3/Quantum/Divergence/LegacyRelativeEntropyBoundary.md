# Legacy Relative-Entropy Boundary

## Abstract

The frozen scalar quantum relative entropy is identified as the finite support-conditioned branch.

**Theorem 1.1 (The frozen scalar expression is the finite branch).**

$$\operatorname{quantumRelativeEntropy}(\operatorname{toLegacy}(\rho), \operatorname{toLegacy}(\sigma)) = \operatorname{finiteTraceLogRelativeEntropy}(\rho, \sigma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/LegacyRelativeEntropyBoundary.legacy_quantumRelativeEntropy_eq_finite_branch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lossless adapters identify the frozen local density-state and channel carriers with the canonical owners, in both directions, without touching the frozen node.

Under these adapters the frozen real-valued trace-log expression is definitionally the finite branch of the support-aware construction.

On an unsupported pair the corrected semantics is infinite while the frozen scalar stays finite; this states the exact semantic boundary of the legacy expression.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/LegacyRelativeEntropyBoundary.legacy_quantumRelativeEntropy_eq_finite_branch`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
