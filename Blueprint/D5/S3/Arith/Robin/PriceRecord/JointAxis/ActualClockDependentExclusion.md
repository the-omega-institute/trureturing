# Exclusion of dependent labels at the actual Robin clock

## Abstract

Every literal Robin budget label in the full exponential denominator range eventually has independent rational bases.

**Theorem 1.1 (Bounds for the first two budget labels).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion.eventually_clock_label_sizes`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion.eventually_clock_label_sizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 37/50 ≤ β < 3/4 and κζ > 0. For all sufficiently large integer e, put R = reference e and Y = exp R. For every real Lbar and w, integer h and integer triple p satisfying |R − Lbar| ≤ 1, 1 ≤ h and jointSquare (boxSizes β κζ Lbar) h p (coordinates Y) w ≤ 43/9, there are natural representatives H, P and Q of h, p 0 and p 1. They satisfy 0 < H, 2H ≤ P, H ≤ Q ≤ 3H and P ≤ 3RH.

The second cutoff offset tends to log(2) and the ratio of the third to the second tends to log(3)/log(2). The literal floor-budget error bounds transfer the resulting phase estimates to the signed labels.

**Theorem 1.2 (Independence throughout the denominator range).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion.eventually_actual_clock_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion.eventually_actual_clock_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same literal budget hypotheses and h ≤ exp(R/50), the rational numbers 3(p 0)/(p 0 + p 1) and 2(p 0)/(p 0 + h) have no equal positive powers. The clock threshold is uniform over Lbar, w, h and p.

The label bounds and denominator cap give log(2P) ≤ R eventually. On the dependent branch the nonzero joint logarithm is at least log(4/3) log(2)/R in absolute value. The joint transport gives a strictly smaller upper bound for all sufficiently large R.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion.eventually_actual_clock_independent`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualClockDependentExclusion.eventually_clock_label_sizes`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualJointAxisLogarithm](ActualJointAxisLogarithm.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence](RationalClockDependence.md)
