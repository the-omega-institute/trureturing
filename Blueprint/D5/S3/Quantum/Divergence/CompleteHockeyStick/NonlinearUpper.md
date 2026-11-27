# Dimension-uniform nonlinear hockey-stick bound

## Abstract

A full span of Kraus products bounds the output divergence for every finite reference and every parameter at least one.

**Theorem 1.1 (Uniform upper bound at positive input divergence).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper.exists_uniform_nonlinear_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper.exists_uniform_nonlinear_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Write x for the input hockey-stick divergence and y for the output divergence. For a channel with full Kraus-product span there is a constant C at least one such that y is at most x minus x squared divided by C squared times (2x + gamma - 1). The same C works for all positive x, all finite references, and all gamma at least one.

The equal reference marginals order the marginals of the positive and negative input parts. The Gram inequality gives purifications related by a contraction on the input and purifier. Lift that contraction through complementary compression, then split its overlap using an optimal output effect and the complementary effect. Cauchy–Schwarz bounds the overlap by the output loss and yields the stated inequality.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper.exists_uniform_nonlinear_upper`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift](UniformLift.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](../ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Divergence/PositiveKrausCompression](../PositiveKrausCompression.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiKernelContraction](../UmegakiKernelContraction.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity](../../Recovery/CanonicalEntanglementFidelity.md)
