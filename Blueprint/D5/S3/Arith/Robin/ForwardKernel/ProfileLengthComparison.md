# Frozen-length profile comparison

## Abstract

Freezing a variable length for bounded Lipschitz profiles has a quadratic error bound.

**Theorem 1.1 (Square bound for a bounded factor).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison.bounded_factor_square_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison.bounded_factor_square_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a measurable factor k is bounded in absolute value by C on an interval [a,b], then the square of the integral of k times f is at most C^2 times the interval length times the integral of f^2. The estimate uses the integral triangle inequality followed by Cauchy-Schwarz.

**Theorem 1.2 (The square error from freezing a profile length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison.variable_profile_square_error_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison.variable_profile_square_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be locally bounded and measurable, let g be an integrable Borel profile bounded by M>=0 and Lipschitz with constant L on [0,1], and let a measurable H lie in [h,h+d] on [a,b], where h>0 and d>=0. If every increment of length u in [0,h+d] has square integral at most V on [a,b], then the square integral of P_H,g minus P_h,g is at most 2*((2M+L)^2+M^2)*d^2*V/h^4. Split the physical interval at h. On its head, the coefficient difference is bounded by (2M+L)*d/h^3; on its tail, the coefficient is bounded by M/h^2. Cauchy-Schwarz bounds both terms, and exchanging the step and starting-point integrals gives the stated constant.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison.bounded_factor_square_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison.variable_profile_square_error_le`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity](MovingLengthRegularity.md)
