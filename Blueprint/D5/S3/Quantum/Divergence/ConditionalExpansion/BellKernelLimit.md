# Bell-kernel limit

## Abstract

The Bell-kernel overlap controls the limit of actual conditional trace-gap ratios.

**Theorem 1.1 (Right-hand limit of the positive trace).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit.bell_kernel_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit.bell_kernel_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B₀ and X₀ be positive semidefinite matrices and Q the orthogonal projection onto the kernel of B₀. As ε decreases to zero through positive values, the trace of the positive part of εX₀ − B₀ divided by ε tends to the real trace of QX₀. The lower estimate tests with Q. The upper estimate uses the inverse square root on the support of B₀ to control the complementary compression and bounds the mixed terms by a positive matrix square.

**Theorem 1.2 (Conditional ratios near the Bell-kernel overlap).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit.exists_bell_kernel_ratio_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit.exists_bell_kernel_ratio_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite channel N with input dimension d ≥ 2, let P be the normalized Bell projector. Take B₀ = amp N(I − P), X₀ = amp N(P), and Q the projection onto the kernel of B₀. For each positive tolerance there are two orthogonal density states on Option A × A with strictly positive input gap at parameter one. Their actual output-to-input conditional gap ratio is at most the real trace of QX₀ plus the tolerance. The padded Bell pair realizes the positive-trace quotient for a sufficiently small ε.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit.bell_kernel_limit`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit.exists_bell_kernel_ratio_le`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper](../CompleteHockeyStick/NonlinearUpper.md)
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation](../CompleteHockeyStickRefutation.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/BellCenteredConditionalTraceGap](BellCenteredConditionalTraceGap.md)
- Dependency: [D5/S3/Quantum/Lieb/SupportPerspectiveTransformer](../../Lieb/SupportPerspectiveTransformer.md)
