# Mechanical Readout Atomic Measure

## Abstract

The completed mechanical readout is the distribution function of a numbered atomic probability measure.

**Theorem 1.1 (Probability and concentration).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_probability_and_carrier`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_probability_and_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive time k, retain all k threshold locations (j-x)/k with their common weight (1-r)^2 r^(k-1). The index records both k and j, so equal locations reached at different times retain separate mass. The geometric mass identity makes the resulting countable Dirac sum a probability measure. Every listed location lies in (0,1] when the phase is in [0,1), and the measure assigns that interval mass one.

**Theorem 1.2 (Distribution function).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On slopes in [0,1], evaluating the atomic measure on the half-line up to the slope gives the completed geometric readout. At each time, the counted atoms are exactly the thresholds crossed by the cumulative floor; summing these finite counts and then all times gives the distribution function.

**Theorem 1.3 (Mass of an interior threshold).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an interior slope, a time k contributes one threshold atom precisely when x+k times the slope is an integer. There is at most one such threshold at each fixed time, while hits at different times all contribute. The singleton mass is the sum of their geometric weights. The interior condition excludes the zero-slope endpoint, where an integer hit can correspond to the omitted index j=0.

**Theorem 1.4 (Closed support).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_support`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the ratio is strictly between zero and one, every numbered threshold has positive mass. At level k, the threshold with index floor(ky)+1 approaches any y in [0,1) as k grows. Closedness adds the upper endpoint, while concentration on (0,1] excludes every point outside [0,1]. Thus the topological support is the full closed unit interval, although the measure is atomic.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_probability_and_carrier`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.geometric_atomic_support`
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutAtomicSeries](MechanicalReadoutAtomicSeries.md)
