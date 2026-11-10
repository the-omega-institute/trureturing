# Cusp averages

## Abstract

Averaged clipped logarithmic cusps and comparison of averaging lengths.

**Theorem 1.1 (Integrability of a cusp increment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.jump_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.jump_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<h<k and arbitrary real q and y, the forward cusp increment as a function of the averaging parameter is integrable on every compact real interval.

**Theorem 1.2 (Monotonicity on the positive axis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.clip_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.clip_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<h<k and 0<=x<=z, the clipped logarithm at x is at most its value at z.

**Theorem 1.3 (Range of the clipped logarithm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.clip_range`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.clip_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<h<k and every real x, the clipped logarithm lies between log(h/k) and zero.

**Theorem 1.4 (Depth bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive h<k, nonnegative length q and nonnegative base y, the average is between zero and log(k/h). These bounds control the lower clipped region in the cross-energy estimate and in moving-length transport.

**Theorem 1.5 (The lower clipped region).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_short_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_short_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<=y<=h and 0<=q<=2h, the cusp average is at most log(3). This bounds the contribution of the lower clipped region to the cross energy and to moving-length transport.

**Theorem 1.6 (Comparison of lengths).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_length_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_length_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For y>=h and 0<r<=q, the averages satisfy B_r(y)<=B_q(y)<=(q/r)B_r(y). The clipped logarithm is increasing and concave above h. This comparison controls moving lengths in CuspMovingLengths.

**Theorem 1.7 (Continuity of the averages).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive h<k and fixed length q, the average is continuous in its base point. The cross-energy integrals use this continuity for compact interval integrability.

**Theorem 1.8 (A short-length upper bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_le_half_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_le_half_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For y>=h and q>=0, the average is at most q/(2y). The inequality log(1+t)<=t and integration of s over the unit interval give this bound, used at the upper endpoint of the cross-energy integral.

**Theorem 1.9 (The short average expansion).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_inner_approx`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_inner_approx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When 2h<=k and h<=y<=k-h, the absolute difference between B_h(y) and h/(2y) is at most h^2/y^2. The one-sided inequality 2t/(t+2)<=log(1+t) applies also at h/y=1. The estimate is consumed by the middle interval of the cross-energy proof.

**Theorem 1.10 (Remaining depth).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_le_log_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_le_log_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h<=y<=k and every length q, the average is at most log(k/y). This controls outer averages in the cross-energy calculation and in moving-length transport.

**Theorem 1.11 (The outer average).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_outer_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_outer_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h<=y<=k, the outer average equals log(k/y)-1+(y/k)(1+log(k/y)). Splitting the affine integral at k and integrating the logarithm gives this formula. It supplies the exact outer integral in CuspCrossEnergy.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.clip_mono`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.clip_range`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_continuous`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_inner_approx`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_le_half_ratio`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_le_log_ratio`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_length_comparison`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_outer_eq`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.cuspAverage_short_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/CuspAverages.jump_integrable`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy](ClippedLogEnergy.md)
