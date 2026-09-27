# Singular Volterra uniqueness

## Abstract

A continuous nonnegative function bounded by its inverse-square-root Volterra integral vanishes on every compact time interval.

**Theorem 1.1 (Vanishing under the singular integral comparison).**

Lean statement: `D5/S3/FluidDynamics/Volterra/SingularKernelUniqueness.eq_zero_of_le_sqrt_kernel_integral`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Volterra/SingularKernelUniqueness.eq_zero_of_le_sqrt_kernel_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T and C be arbitrary nonnegative real numbers, and let d be a real-valued function on the real line that is continuous and nonnegative on the closed interval from zero to T. For every t in this interval, suppose that d at t is at most C times the Lebesgue interval integral, from zero to t, of d at s multiplied by the reciprocal of the square root of t minus s. Then d vanishes at every point of the closed interval, including both endpoints. The statement includes T equal to zero and C equal to zero. The reciprocal uses the total real inverse, whose value at zero is zero.

The inverse-square-root kernel is integrable because its power exponent is greater than minus one. Reflection and continuity on the compact interval give integrability of each comparison integrand. Multiplying the kernel by an exponentially decreasing weight gives integral masses tending to zero by dominated convergence. Choose the weight so that C times its mass is less than one. The corresponding weighted function attains a nonnegative maximum on the compact interval; the integral comparison bounds this maximum by that same strict factor times itself. The maximum is therefore zero, and positivity of the exponential weight gives pointwise vanishing.

## References

- Truth anchor: `D5/S3/FluidDynamics/Volterra/SingularKernelUniqueness.eq_zero_of_le_sqrt_kernel_integral`
