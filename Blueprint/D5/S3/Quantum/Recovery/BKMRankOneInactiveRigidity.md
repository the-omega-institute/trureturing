# Rank-one BKM gap and the active retained span

## Abstract

Active and inactive blocks at zero actual BKM gap for a rank-one observable.

**Theorem 1.1 (The faithful auxiliary density on the active span).**

Lean statement: `D5/S3/Quantum/Recovery/BKMRankOneInactiveRigidity.bkmGap_rankOne_eq_zero_iff_activeBlock`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMRankOneInactiveRigidity.bkmGap_rankOne_eq_zero_iff_activeBlock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a faithful trace-one joint matrix, S its actual retained partial trace, and w a unit retained vector. For every distinct eigenvalue of S, take the component of w in its full eigenspace. The projection P onto the span of these components is the sum of their normalized outer products, with a zero component contributing zero. Let Q be its complement and B the joint relative density formed with the lifted inverse square root of S. The BKM gap for the rank-one projection of w vanishes exactly when B is the sum of P tensored with a unique positive definite trace-one auxiliary matrix and the compression of B by the lift of Q. This compression has actual retained partial trace Q and is positive definite on the range of the lifted Q.

Use the grouped modular equality criterion on every auxiliary matrix slice. The sum of the ratio groups gives scalar action on w. If some spectral component fails to have this same scalar action, take a largest eigenvalue with a nonzero error and divide it by the smallest eigenvalue with a nonzero component of w. In the test for this ratio, higher errors vanish and smaller eigenvalues cannot pair with an occupied component. The coefficient of the remaining error is the squared norm at the smallest occupied eigenvalue, which is positive. This argument permits repeated eigenvalues and colliding ratios. Compress B along the isometry that tensors each auxiliary vector with w to obtain the faithful active density. The actual partial trace of B is the identity, giving the two trace conditions. The nonzero projection P makes the auxiliary factor unique. Conversely the grouped ratio matrices are supported on P, so the two-block form commutes with every lifted ratio matrix.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMRankOneInactiveRigidity.bkmGap_rankOne_eq_zero_iff_activeBlock`
- Dependency: [D5/S3/Quantum/Recovery/BKMObservableProductRigidity](BKMObservableProductRigidity.md)
