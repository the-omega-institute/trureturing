# Continuation from the hard-core fiber to actual seven-site states

## Abstract

Continuation from the hard-core fiber to actual seven-site states

**Theorem 1.1 (Continuation from the hard-core fiber to actual seven-site states).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphContinuation.exists_open_dense_actual_state_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphContinuation.exists_open_dense_actual_state_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a compact subset of the seven-site trace graph has Hausdorff dimension at most six, contains the chart boundary and leaves an injective real derivative of the observation at each ordinary chart point outside it. The compact state source then has a relatively open dense set consisting of actual projectors, each identified by its adjacent two-site marginal against every projector in the compact closure.

Over a neighborhood of the hard-core state, the full projector determines its graph lift. The nearby unique marginal fibers supply a nonempty open set of singleton graph fibers. This set meets the dense region left after discarding the observation values of the exceptional set. Continuation applies in the eight-real-dimensional chart with nine real readings.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphContinuation.exists_open_dense_actual_state_recovery`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation](CompactRegularFiberContinuation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteActualSourceChart](SevenSiteActualSourceChart.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphReadout](SevenSiteGraphReadout.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLinearTraceLift](SevenSiteLinearTraceLift.md)
