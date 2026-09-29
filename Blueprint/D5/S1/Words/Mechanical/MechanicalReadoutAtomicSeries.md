# Mechanical Readout Atomic Series

## Abstract

The completed mechanical readout has an absolutely summable floor expansion with unit atomic mass.

**Theorem 1.1 (Floor series and mass normalization).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a geometric ratio in [0,1), a slope in [0,1], and a phase in [0,1). The completed readout is the sum, over positive times k, of the actual cumulative floor at time k weighted by (1-r)^2 r^(k-1). The sum of these weights multiplied by k is exactly one. Absolute summability follows from the bound of the cumulative floor by k. The proof expands each actual mechanical letter as the difference of two successive floors, shifts the convergent series, and evaluates the linearly weighted geometric series. At time k the floor equals the number of thresholds (i-x)/k, for i from one through k, that the slope has crossed. Substitution gives an exact atomic distribution-function series. Constructing its probability measure and identifying the exact jumps require further arguments.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutAtomicSeries.geometric_readout_floor_series_and_mass`
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutOrder](MechanicalReadoutOrder.md)
