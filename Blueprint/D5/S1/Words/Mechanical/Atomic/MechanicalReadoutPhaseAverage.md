# Mechanical Readout Phase Average

## Abstract

Uniform phase averaging of the numbered atomic measure is Lebesgue measure on the unit interval.

**Theorem 1.1 (Uniform phase average).**

Lean statement: `D5/S1/Words/Mechanical/Atomic/MechanicalReadoutPhaseAverage.geometric_atomic_phase_average`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/Atomic/MechanicalReadoutPhaseAverage.geometric_atomic_phase_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ratio 0 < r < 1 and every measurable subset of [0,1], integrating the actual numbered atomic measure over phases in [0,1) gives its Lebesgue measure. Each level partitions (0,1] into equal cells under its threshold maps; the geometric mass identity then sums the cell contributions to one. The statement uses the half-open phase domain of the mechanical word and allows arbitrary measurable sets within the closed unit interval.

## References

- Truth anchor: `D5/S1/Words/Mechanical/Atomic/MechanicalReadoutPhaseAverage.geometric_atomic_phase_average`
- Dependency: [D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure](../MechanicalReadoutAtomicMeasure.md)
