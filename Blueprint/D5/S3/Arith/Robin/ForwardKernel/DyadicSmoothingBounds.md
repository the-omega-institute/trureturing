# Bounds for dyadic smoothing

## Abstract

Uniform smoothing estimates.

**Theorem 1.1 (Uniform smoothing estimates).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.dyadic_smoothing_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.dyadic_smoothing_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and measurable, h>0, A>=0, a<=b, L<=a, and b+4k<=U. Suppose the L2 norm of D_u E on [L,U] is at most A*sqrt(u) for every h<=u<=8k. Simultaneously for every h<=R<=2k, the L2 norms on [a,b] of B_R, its derivative, and the derivative of Z_R are at most 2A*sqrt(R), 4A/sqrt(R), and 2A/sqrt(R), respectively. Pointwise on [a,b], the absolute values of B_R and the derivative of Z_R are at most 2A and 2A/R. All translations are bounded using the larger interval [L,U]. Taking A to be a fixed multiple of sqrt(X*log(X)) gives the five estimates in (491.5).

**Theorem 1.2 (Small-scale residual bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.smoothing_residual_intervalL2_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.smoothing_residual_intervalL2_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and measurable, h>0, A>=0, a<=b, L<=a, and b+2h<=U. If every increment of length between zero and 2h has L2 norm on [L,U] at most A*sqrt(h), then E-Z_h has L2 norm on [a,b] at most 2A*sqrt(h). Decompose the residual into E-A_h E and its forward average, and apply Cauchy-Schwarz and Fubini to the first residual.

**Theorem 1.3 (Residual and block smoothing estimates).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.dyadic_smoothing_bounds_with_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.dyadic_smoothing_bounds_with_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With explicit inner and working intervals, a uniform square-root increment bound on the working interval gives both the double-average residual estimate and the five simultaneous smoothing block and derivative estimates on the inner interval.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.dyadic_smoothing_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.dyadic_smoothing_bounds_with_residual`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.smoothing_residual_intervalL2_le`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingIdentities](DyadicSmoothingIdentities.md)
