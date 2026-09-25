# Pure-qubit affine geometry

## Abstract

A rank-two affine measurement of a pure qubit curve has a strict arc parametrization.

**Definition 1.1 (Spectral SLD information).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.spectralQFI`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.spectralQFI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In an eigenbasis of the positive semidefinite state, sum twice the squared modulus of each derivative entry divided by the sum of the corresponding eigenvalues. Terms with zero denominator are zero. Positivity on a two-sided neighborhood forces the derivative's kernel-to-kernel block to vanish (Pker D Pker = 0).

**Definition 1.2 (Guarded real infimum).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.guardedInfimum`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.guardedInfimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real infimum with explicit nonempty and bounded-below guard.

**Definition 1.3 (Canonical density-state bridge).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.densityBridge`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.densityBridge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one matrix is constructed as a canonical density state, with exact equality of the recovered matrix.

**Definition 1.4 (Full actual program class).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.IsProgram`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.IsProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed finite POVM and a continuously differentiable pure state curve are defined on an open connected interval containing the closed radius interval. Born probabilities are exactly affine and positive throughout. The cost is the actual spectral SLD information at zero. No readout rank, score sign, canonical arc, or zero-score effect shape is imposed.

**Definition 1.5 (Attainable actual costs).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.costs`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.costs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set ranges over all actual programs in the preceding class.

**Definition 1.6 (Cost infimum).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.C2`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.C2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum is used only in the branch with nonempty and lower-bounded cost set. Both conditions hold at every sufficiently small positive radius.

**Definition 1.7 (Bloch vector).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three real Bloch coordinates of a two by two matrix.

**Definition 1.8 (Bloch matrix).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hermitian matrix with a specified real trace and Bloch vector.

**Definition 1.9 (Visible readout map).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effectReadout`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.effectReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors.

**Definition 1.10 (Orthogonal change of Bloch coordinates).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframe`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An orthogonal change of the Bloch vector preserves the trace coordinate.

**Definition 1.11 (Linear Bloch map).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch coordinates form a real linear map on complex matrices.

**Definition 1.12 (Linear change of matrix coordinates).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframeLinear`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframeLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed orthogonal Bloch frame induces a real linear map on matrices.

**Definition 1.13 (Small quadratic root).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.root`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores.

**Definition 1.14 (Radius map).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.radiusMap`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.radiusMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius includes a strict margin inside the pure-state arc and is locally inverted near zero.

**Definition 1.15 (Extended family cost).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.extendedCost`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.extendedCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost formula extends through the zero transverse parameter for the normalization branch.

**Definition 1.16 (Upper diagonal coefficient).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.upperDiag`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.upperDiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complementary quadratic root determines the upper diagonal effect coefficient.

**Definition 1.17 (Actual effect matrix).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effect`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two diagonal coefficients and the normalized direction determine each effect matrix.

**Definition 1.18 (Pure-state arc).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.arc`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.arc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate.

**Theorem 1.19 (Actual rank-two arc and feasible coefficients).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitGeometry.actual_rank_two_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitGeometry.actual_rank_two_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual rank-two affine readout of a pure curve admits a fixed orthonormal frame. The invisible coordinate has constant sign on the connected open interval. The effect coefficients satisfy positivity, normalization, and the exact affine-readout relations; the visible coordinate satisfies the strict radius bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.C2`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.IsProgram`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.actual_rank_two_parameters`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.arc`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.costs`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.densityBridge`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effect`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effectReadout`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.extendedCost`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.guardedInfimum`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.radiusMap`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframe`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframeLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.root`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.spectralQFI`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.upperDiag`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
