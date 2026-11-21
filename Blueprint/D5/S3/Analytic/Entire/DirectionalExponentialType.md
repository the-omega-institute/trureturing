# Directional exponential type

## Abstract

Real-axis boundedness directs exponential growth into the imaginary coordinate.

**Theorem 1.1 (Exact directional bound).**

Lean statement: `D5/S3/Analytic/Entire/DirectionalExponentialType.norm_le_exp_abs_im`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/DirectionalExponentialType.norm_le_exp_abs_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let an entire function F have real-axis bound B and radial bound C times (1 + |z|) to the power m times exp(a |z|), with a nonnegative. Its norm is bounded by max(B,C) times (1 + |z|) to the power m times exp(a |Im z|). In each half-plane the quotient by (1 minus or plus iz) to the power m cancels the polynomial growth on the imaginary ray, while an exponential factor cancels the exact radial rate on that ray. The four Phragmen-Lindelof quadrant theorems bound the two quotients. Recovering the original function preserves both a and m.

## References

- Truth anchor: `D5/S3/Analytic/Entire/DirectionalExponentialType.norm_le_exp_abs_im`
