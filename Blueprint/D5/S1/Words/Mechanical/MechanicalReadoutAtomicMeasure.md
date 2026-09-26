# Mechanical Readout Atomic Measure

## Abstract

The completed mechanical readout is the distribution function of a numbered atomic measure.

**Theorem 1.1 (Distribution function).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On slopes in [0,1], evaluating the atomic measure on the half-line up to the slope gives the completed geometric readout. At each time, the counted atoms are exactly the thresholds crossed by the cumulative floor; summing these finite counts and then all times gives the distribution function.

**Theorem 1.2 (Mass of an interior threshold).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an interior slope, a time k contributes one threshold atom precisely when x+k times the slope is an integer. There is at most one such threshold at each fixed time, while hits at different times all contribute. The singleton mass is the sum of their geometric weights. The interior condition excludes the zero-slope endpoint, where an integer hit can correspond to the omitted index j=0.

**Theorem 1.3 (Exact left jump).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As a slope approaches an interior value from below, the measures of its closed threshold half-lines converge to the measure of the open half-line at that value. The completed readout therefore has a real left limit equal to that open-half-line mass. Its value at the slope exceeds the limit by exactly the singleton mass, hence by the real sum of the weights at every integer-hit time. Coincident hits are retained.

**Theorem 1.4 (Reduced rational jump).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero phase and a reduced interior slope p/q, positive integer hits occur exactly at multiples of q. Splitting the actual hit-weight series after its first q terms gives a q-step tail recurrence. Its first block contains only the weight at time q, and solving the recurrence yields the left jump (1-r)^2 r^(q-1)/(1-r^q). The left limit is the real limit supplied by the atomic distribution function.

**Theorem 1.5 (Closed support).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_support`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the ratio is strictly between zero and one, every numbered threshold has positive mass. At level k, the threshold with index floor(ky)+1 approaches any y in [0,1) as k grows. Closedness adds the upper endpoint, while concentration on (0,1] excludes every point outside [0,1]. Thus the topological support is the full closed unit interval, although the measure is atomic.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_support`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact`
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutAtomicSeries](MechanicalReadoutAtomicSeries.md)
