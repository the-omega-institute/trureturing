# Local variance from the cumulative variance band

## Abstract

Local variance from the cumulative variance band

**Theorem 1.1 (Eventual window bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.variance_window_eventually`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.variance_window_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform cumulative variance asymptotic implies that for every positive epsilon, all sufficiently large X satisfy the relative error bound simultaneously for Y in [X/2,4X] and Y^alpha<=v<=Y^beta. No convergence rate is required.

**Theorem 1.2 (Local square integral with an interval length term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.local_variance_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.local_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be measurable and bounded on compact intervals, and let 0<alpha<theta<beta<1. Suppose X>=4, R>0, epsilon>=0, [A,B] is contained in [X/2,4X], (4X)^alpha<=R, and 4R<=(X/2)^beta. If the window relative error is at most epsilon, then for every R<=v<=4R the integral of (E(y+v)-E(y))^2 over [A,B] is at most v*log(X)*(3*(B-A)+16*epsilon*X). Subtract the cumulative variances at B and A. The logarithmic inequality log(t)<=t-1 bounds the main difference, while both endpoint errors are bounded using A+B<=8X and log(Y/v)<=2*log(X).

**Theorem 1.3 (Moving endpoints under a local variance bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.local_endpoint_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.local_endpoint_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two differentiable endpoints in [A,B] whose derivatives are at least m>0 and whose absolute gap is at most R, the window variance bound gives an integral of their squared E-difference at most (20R/m)*log(X)*(3*(B-A)+16*epsilon*X). The interval length remains explicit. Apply the signed endpoint estimate with C=log(X)*(3*(B-A)+16*epsilon*X).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.local_endpoint_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.local_variance_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/LocalVarianceBand.variance_window_eventually`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs](MacroscopicVarianceDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance](MovingEndpointVariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
- Dependency: [D5/S3/Quantum/Schatten/PowerMajorization](../../../Quantum/Schatten/PowerMajorization.md)
