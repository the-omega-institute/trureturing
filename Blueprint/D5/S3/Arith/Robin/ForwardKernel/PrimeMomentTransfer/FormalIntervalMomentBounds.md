# Formal interval moment bounds

## Abstract

Uniform interval correlation estimates bound the formal cubic and fourth values.

**Definition 1.1 (interval weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.intervalWeight`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.intervalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real scale H, a finite set S of natural numbers and real endpoints a,b, the interval weight on S is one exactly at natural shifts d satisfying floor(aH) < d <= floor(bH), with both floors taken in the natural numbers, and zero elsewhere.

**Definition 1.2 (is interval weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.IsIntervalWeight`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.IsIntervalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coefficient function on a finite shift set is an interval weight in [0,M] at scale H when it equals intervalWeight for some 0 <= a <= b <= M. Membership uses natural floors; for nonnegative H this agrees with the indicator of (aH,bH].

**Theorem 1.3 (is interval weight mul).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative H, the product of two interval weights in [0,M] is again such an interval weight. The intersection uses lower endpoint max(a,c) and upper endpoint max(max(a,c),min(b,d)), so disjoint intervals give the empty interval.

**Theorem 1.4 (interval points subset).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_points_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_points_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative H and b <= M, every positive integer shift in (aH,bH] is at most floor(MH).

**Theorem 1.5 (distinct interval weight moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.distinct_interval_weight_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.distinct_interval_weight_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative H and ordered interval endpoints in [0,M], the formal distinct moment of their interval weights on the natural shifts at most floor(MH), with singular-series data transported along inclusion, equals their distinct centered interval correlation.

**Theorem 1.6 (interval weight family).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_weight_family`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_weight_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of interval weights in [0,M] at scale H can be represented by two endpoint functions a,b, with 0 <= a_i <= b_i <= M for every index.

**Theorem 1.7 (index interval weight bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.index_interval_weight_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.index_interval_weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative H, the absolute sum of an interval weight in [0,M] over the natural shifts at most floor(MH) is at most M H.

**Theorem 1.8 (Covariance product error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_product_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_product_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two factors have errors bounded by D H and their leading terms are bounded by M H L, with L at least one, their product error is at most (2 M D plus D squared) H squared L.

**Theorem 1.9 (Cardinality bound for a scaled interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_points_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_points_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative H and endpoints 0 <= a <= b <= M, the number of positive integer shifts in (aH,bH] is at most M times H.

**Theorem 1.10 (Bounds for an overlap length).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.sigma_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.sigma_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M is nonnegative, a and c are nonnegative, and b is at most M, the nonnegative overlap length max(0,min(b,d)-max(a,c)) is at most M.

**Theorem 1.11 (Uniform second formal values).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_second_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_second_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive alpha, beta below one, M at least one, singular-series values one on empty sets and singletons, and the interval correlation input, there is a nonnegative C such that eventually |Phi(SS,H,s,a,b,a,b)| is at most C H log N for every N^alpha<=H<=N^beta, log N<=s<=log N+log 2 and 0<=a<=b<=M. The estimate uses the second correlation bound and the diagonal overlap count.

The finite signed-cube realization identifies Phi with the formal coefficient moment. Products of interval indicators are again interval indicators, including when their intersection is empty. The number of lattice points in an overlap differs from H times its length by at most two. Consequently the second formal moment differs from H(s-log H) times the overlap length by O(H). The cubic identity and the full fourth pairing-defect identity then control every repeated-index term. On the polynomial length band, (log N)^2 is eventually at most H, so H(log N)^3 is at most H^2 log N. The fourth main term is the sum of the three products of overlap lengths, multiplied by H^2(s-log H)^2.

**Theorem 1.12 (Uniform cubic and fourth formal values).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_moment_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_moment_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 0<alpha<beta<1, let the singular series equal one on the empty set and every singleton, and assume the uniform interval correlation estimates. For every M at least one there is a nonnegative constant C and a nonnegative modulus eta, antitone on [2,infinity) and tending to zero, such that eventually for all N^alpha<=H<=N^beta and log N<=s<=log N+log 2, writing L=log N, the absolute cubic formal value is at most C[eta(H)(HL)^(3/2)+HL^2]. The absolute difference of the fourth formal value from H^2(s-log H)^2 W4 is at most C[eta(H)H^2 L^2+H^2 L]. Both estimates hold uniformly over all ordered interval endpoints in [0,M], allowing empty intervals and arbitrary overlaps.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.IsIntervalWeight`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.distinct_interval_weight_moment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_moment_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.formal_interval_second_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_points_card_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.geom_product_error`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.index_interval_weight_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.intervalWeight`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_points_subset`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_weight_family`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.mul`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.sigma_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel](SignedCubeMomentModel.md)
