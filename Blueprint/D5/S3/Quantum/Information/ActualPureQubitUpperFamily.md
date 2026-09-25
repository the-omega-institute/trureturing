# Actual pure-qubit upper family

## Abstract

Normalized positive effect matrices and pure-state arcs give a matching upper family.

**Theorem 1.1 (Normalized positive effect family).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_effect_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_effect_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any normalized centered direction, the quadratic small roots admit a differentiable normalization branch and a local inverse radius map. Along the same family the actual effects are positive semidefinite and sum to the identity, the strict arc and probability margins hold, and the extended cost has the required moment limit.

**Theorem 1.2 (Matching family of actual programs).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_upper_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_upper_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive finite probabilities and a centered direction of unit weighted second moment, the radius family gives actual POVMs and pure curves. Their spectral cost excess has the stated moment coefficient. Scaling the direction in the infimum theorem gives the original affine data.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_effect_family`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_upper_family`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
