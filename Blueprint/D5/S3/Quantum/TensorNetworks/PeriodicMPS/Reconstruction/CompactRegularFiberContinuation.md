# Generic singleton fibers on a compact source

## Abstract

Generic singleton fibers on a compact source

**Theorem 1.1 (Generic singleton fibers on a compact source).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation.compact_generic_recovery_of_dimH_bad`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation.compact_generic_recovery_of_dimH_bad` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Lipschitz observation on a compact metric source has an open dense singleton-fiber locus under the stated chart and seed hypotheses. The connected dense ordinary locus is covered by charts with Lipschitz inverses. Away from the compact exceptional set, the chart observation is a real-analytic immersion into a space of dimension one higher than the chart.

The exceptional set has Hausdorff dimension at most the chart dimension minus two. The argument removes every fiber meeting that set and proves that the remaining locus is open, dense and path connected. One singleton in the remaining locus supplies the seed for analytic continuation. Each fiber in the conclusion is taken over the full compact source.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation.compact_generic_recovery_of_dimH_bad`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Geometry/HausdorffCodimTwoComplement](../Geometry/HausdorffCodimTwoComplement.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSCompactAnalyticCharts](../PeriodicMPSCompactAnalyticCharts.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSImmersionPullback](../PeriodicMPSImmersionPullback.md)
