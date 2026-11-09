# The fourth-moment band hypothesis

## Abstract

Uniform fourth moments of fixed increments on an exponent band.

**Definition 1.1 (Uniform fourth-moment upper bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs.FourthMomentBandBoundFor`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs.FourthMomentBandBoundFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write D_u(x)=E(x+u)-E(x). The constant C4 is nonnegative, and for all sufficiently large Y, simultaneously for every Y^alpha<=u<=Y^beta, the integral of abs(D_u(x))^4 from 1 to Y is at most C4*Y*u^2*log(Y/u)^2. The threshold for Y is independent of u. This is the undivided form of the fourth-moment hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthMomentBandDefs.FourthMomentBandBoundFor`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
