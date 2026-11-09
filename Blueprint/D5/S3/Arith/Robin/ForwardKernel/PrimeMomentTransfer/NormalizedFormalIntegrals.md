# Normalized formal integrals

## Abstract

Weighted normalized estimates for formal cubic and fourth moments.

**Theorem 1.1 (Integration of the cubic envelope).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals.integrated_third_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals.integrated_third_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose N is at least two, H is positive, C and E are nonnegative, and w has supported bounded variation norm at most B. If the absolute formal cubic moment on [N,2N] is at most C times the sum of E times (H log N) to the power three halves and H times log N squared, its weighted integral divided by N times (H log N) to the power three halves has absolute value at most C B times the sum of E and the square root of log N divided by H.

**Theorem 1.2 (Integration of the fourth envelope).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals.integrated_fourth_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals.integrated_fourth_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose N is at least two, H is positive, C and E are nonnegative, and w has supported bounded variation norm at most B. If the difference between the formal fourth moment and H squared times (log x minus log H) squared times the fourth overlap pairing is uniformly bounded by C times the sum of E H squared log N squared and H squared log N, the difference between their weighted integrals after normalization is at most C B times the sum of E and the reciprocal of log N.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals.integrated_fourth_envelope`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals.integrated_third_envelope`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra](NormalizationAlgebra.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools](WeightedIntegralTools.md)
