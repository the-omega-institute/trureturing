# Trace of a Corrected Ground Charge Cycle

## Abstract

Actual cyclic ground-orbit power traces with the retained cocycle phase.

For an integral symmetric even-diagonal lattice and an additive isometry preserving the bilinear form, take one actual first-return charge orbit of a norm-four ground state. The span of its distinct zero-oscillator ground vectors is finite and carries the corrected lift power.

The action on each orbit basis vector is the literal product of the one-step cocycle and sign phases. The trace is the sum of the phases exactly when the power returns the orbit, and is zero for a non-returning power because the cyclic shift has no diagonal entries.

**Theorem 1.1 (Returning powers have the literal phase sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitTrace.corrected_ground_cycle_power_trace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitTrace.corrected_ground_cycle_power_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof computes the actual LinearMap.trace in the finite orbit basis. It retains the correctedGroundPhase cocycle product and separates the divisibility case from the zero-trace non-returning case.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitTrace.corrected_ground_cycle_power_trace`
- Dependency: [D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitFixedSpace](CyclicGroundOrbitFixedSpace.md)
