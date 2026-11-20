# Recovering the weighted trace lift from the full seven-site projector

## Abstract

Recovering the weighted trace lift from the full seven-site projector

**Theorem 1.1 (Recovering the weighted trace lift from the full seven-site projector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLinearTraceLift.lift_eq_of_readColumn_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLinearTraceLift.lift_eq_of_readColumn_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply six fixed seven-letter trace contrasts to a column of the full state projector. On ordinary trace amplitudes these contrasts give one common multiple of the six weighted trace coordinates.

At a point of the compact graph, if the first component of the resulting vector is nonzero, its projector is the weighted trace projector in the graph. The identity passes to graph limits by continuity. In this region the full state projector has a unique graph lift.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLinearTraceLift.lift_eq_of_readColumn_ne_zero`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactGraph](SevenSiteCompactGraph.md)
