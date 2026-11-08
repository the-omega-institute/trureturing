# Fourth-moment endpoint estimate

## Abstract

Local fourth energy controls normalized moving and frozen increments.

**Theorem 1.1 (Fourth energy between moving endpoints).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentEndpoint.local_fourth_endpoint_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentEndpoint.local_fourth_endpoint_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the fourth powers of fixed increments have local energy at most C times v squared times log(X) squared times the window length plus the uniform error. For increasing endpoint functions with derivatives at least m and signed gap at most R, their fourth-power difference integral is at most (656/3)(C/m)R squared log(X) squared times the image interval length plus the error. Averaging the common-endpoint identity over [2R,3R] and [R,4R] uses the shared even-power endpoint estimate. The two quadratic integrals sum to (82/3)R cubed, giving exactly 656/3.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentEndpoint.local_fourth_endpoint_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentTransferDefs](FourthMomentTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance](../MovingEndpointVariance.md)
