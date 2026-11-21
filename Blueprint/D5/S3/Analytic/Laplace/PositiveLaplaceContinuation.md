# Positive Laplace convergence across the possible abscissa

## Abstract

Convergence of a positive Laplace transform from real regularity of its meromorphic continuation

**Theorem 1.1 (Convergence, holomorphy and agreement of germs).**

Lean statement: `D5/S3/Analytic/Laplace/PositiveLaplaceContinuation.integrable_and_analytic_of_meromorphic_continuation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PositiveLaplaceContinuation.integrable_and_analytic_of_meromorphic_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let μ be a measure on a measurable space Ω, and let X : Ω → ℝ be AEMeasurable for μ and nonnegative μ-almost everywhere. Let a and b be real and suppose exp(−bX) is μ-integrable. Write L(z) for complexMGF X μ (−z), the actual Laplace integral of exp(−zX). Suppose H : ℂ → ℂ is meromorphic on Re(z)>a and analytic at each real x with a<x≤b. At some complex z₀ with a<Re(z₀) and b<Re(z₀), assume H and L agree on a neighborhood of z₀.

Then exp(−xX) is integrable for every real x>a, and L is holomorphic on Re(z)>a. At each complex z of that half-plane, exp(−zX) is integrable, H agrees with L on a punctured neighborhood of z, and H(z)=L(z) whenever H is continuous at z.

The real convergence set is upward closed because X≥0 almost everywhere. If convergence failed at x>a, the set would have an infimum σ with a<x≤σ≤b. PositiveEulerContinuation.analytic_laplace gives holomorphy to the right of σ. The meromorphic identity theorem propagates the local agreement as equality of punctured germs throughout that half-plane. Analyticity of H at σ and continuity upgrade the agreement on the right portion of a disk around σ to pointwise equality. This gives the holomorphic extension excluded by AbscissaSingularity.no_holomorphic_extension_at_abscissa. Once convergence holds throughout Re(z)>a, the same identity argument gives the stated germ equality and the pointwise equality at continuity points.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/PositiveLaplaceContinuation.integrable_and_analytic_of_meromorphic_continuation`
- Dependency: [D5/S3/Analytic/Laplace/PositiveEulerContinuation](PositiveEulerContinuation.md)
