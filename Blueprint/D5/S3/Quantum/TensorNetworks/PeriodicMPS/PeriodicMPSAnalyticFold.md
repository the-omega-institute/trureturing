# Generic separation for an analytic fold

## Abstract

Generic separation for an analytic fold

**Theorem 1.1 (Singleton fibers after adding a residual readout).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticFold.exists_generic_singleton_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticFold.exists_generic_singleton_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider a real-analytic observation with horizontal coordinates and one vertical variable. If the first vertical derivative of a scalar readout vanishes and its second vertical derivative is nonzero, it has a strict fold after shrinking the chart. Suppose there are pairs arbitrarily near the base point that share the horizontal and fold values and differ in a further analytic readout. The analytic identity principle confines branch coincidence to a nowhere dense set. On a smaller open source neighborhood, an open dense set of targets has singleton fibers within that neighborhood for the augmented observation.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticFold.exists_generic_singleton_fibers`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticBranchSeparation](PeriodicMPSAnalyticBranchSeparation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSLocalObservationGraph](PeriodicMPSLocalObservationGraph.md)
