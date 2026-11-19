# Fourth pairing integral

## Abstract

Weighted approximation of the fourth logarithmic pairing integral.

**Theorem 1.1 (Uniform approximation of the fourth main term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FourthMainIntegral.fourth_main_integral_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FourthMainIntegral.fourth_main_integral_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be at least two, let one be at most H at most N, and let four ordered intervals lie in [0,M] with M nonnegative. For a supported bounded variation weight of norm at most B, the integral over [N,2N] of w(x/N) times the squared ratio (log x minus log H)/log N times the fourth overlap pairing differs from N times the mean of w on [1,2] times kappa(N,H) squared times that pairing by at most N B times 9 M squared log 2 divided by log N. The estimate follows by integrating the logarithmic square error and bounding the fourth overlap pairing by 3 M squared.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FourthMainIntegral.fourth_main_integral_error`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow](LogWindow.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools](WeightedIntegralTools.md)
