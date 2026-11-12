# Cyclic monitored power contraction

## Abstract

The actual cyclic monitored operator has a strictly contracting power.

**Theorem 1.1 (A strict power bound derived from actual cyclicity).**

$$\exists N\ge1,\quad\exists q, 0\le q<1,\quad \left\lVert T_C^N \right\rVert\le q$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredPowerBound.cyclic_power_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite dimensional complex Hilbert space, every unitary U and every unit vector v, C is the actual span of U^n v, and T_C is the restriction of (I-P_v)U. No stability or independent cyclicity hypothesis is imposed. The actual cyclic future-kernel theorem proves zero dark space. Orthogonal coordinates carry T_C and the actual click restriction to a conservative singleton instrument. FiniteDetectionSurvivalLimit.dark_block_contraction then supplies the strict gap; its estimate is reused directly. The chosen N is dim C and q is the norm of T_C^N. This proves the registered contraction witness. It does not assert the infinite weighted return identity or identify dim C with occupied spectral cardinality. The complete monitored-return endpoint is classical, as in Grunbaum, Velazquez, Werner and Werner, arXiv:1202.3903v3, Theorem 2.

## References

- Truth anchor: `D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredPowerBound.cyclic_power_contraction`
- Dependency: [D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit](../../Quantum/Measurement/FiniteDetectionSurvivalLimit.md)
- Dependency: [D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredContraction](CyclicMonitoredContraction.md)
