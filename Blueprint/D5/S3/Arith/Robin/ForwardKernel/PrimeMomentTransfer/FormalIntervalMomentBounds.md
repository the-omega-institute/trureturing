# Formal interval moment bounds

## Abstract

Uniform interval correlation estimates bound the formal cubic and fourth values.

**Theorem 1.1 (Cardinality bound for a scaled interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_points_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_points_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative H and endpoints 0 <= a <= b <= M, the number of positive integer shifts in (aH,bH] is at most M times H.

**Theorem 1.2 (Bounds for an overlap length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.sigma_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.sigma_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M is nonnegative, a and c are nonnegative, and b is at most M, the nonnegative overlap length max(0,min(b,d)-max(a,c)) is at most M.

The finite signed-cube realization identifies Phi with the formal coefficient moment. Products of interval indicators are again interval indicators, including when their intersection is empty. The number of lattice points in an overlap differs from H times its length by at most two. Consequently the second formal moment differs from H(s-log H) times the overlap length by O(H). The cubic identity and the full fourth pairing-defect identity then control every repeated-index term. On the polynomial length band, (log N)^2 is eventually at most H, so H(log N)^3 is at most H^2 log N. The fourth main term is the sum of the three products of overlap lengths, multiplied by H^2(s-log H)^2.

**Theorem 1.3 (Uniform cubic and fourth formal values).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_moment_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_moment_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 0<alpha<beta<1, let the singular series equal one on the empty set and every singleton, and assume the uniform interval correlation estimates. For every M at least one there is a nonnegative constant C and a nonnegative modulus eta, antitone on [2,infinity) and tending to zero, such that eventually for all N^alpha<=H<=N^beta and log N<=s<=log N+log 2, writing L=log N, the absolute cubic formal value is at most C[eta(H)(HL)^(3/2)+HL^2]. The absolute difference of the fourth formal value from H^2(s-log H)^2 W4 is at most C[eta(H)H^2 L^2+H^2 L]. Both estimates hold uniformly over all ordered interval endpoints in [0,M], allowing empty intervals and arbitrary overlaps.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_moment_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_points_card_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.sigma_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel](SignedCubeMomentModel.md)
