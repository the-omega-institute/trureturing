# Golden Cofinal Kernel Criterion

## Abstract

A cofinal vanishing-scale kernel family is positive semidefinite exactly under RH.

**Theorem 1.1 (Cofinal kernel positivity is equivalent to RH).**

$$\begin{aligned}omega_{n} \Rightarrow 0,\\RiemannHypothesis \iff \forall n \ge 0, \operatorname{PosSemidef}\left(K_{omega_{n}}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CofinalSupport/GoldenCofinalKernelCriterion.golden_cofinal_kernel_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each scale, positivity means that every finite sampled Gram matrix of the supplied complex kernel is positive semidefinite. The theorem assumes the Hermite-Biehler forward implication and identifies each kernel diagonal with the canonical shifted-xi diagonal value.

For the reverse implication, a right-half-strip zeta zero determines a positive displacement delta. Since omega_n tends to zero, sampled points approach the zero through a punctured neighborhood. Isolated zeros provide an index where the shifted xi value is nonzero, and the existing one-point formula gives a strictly negative diagonal entry, contradicting positive semidefiniteness.

The positivity of every omega_n is explicit; it excludes Lean's totalized division at zero in the one-point formula.

## References

- Truth anchor: `D5/S3/Weil/CofinalSupport/GoldenCofinalKernelCriterion.golden_cofinal_kernel_criterion`
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../ZetaBridge/RightHalfStripRiemannReduction.md)
- Dependency: [D5/S3/Weil/ZetaCore/OffLinePickWitness](../ZetaCore/OffLinePickWitness.md)
