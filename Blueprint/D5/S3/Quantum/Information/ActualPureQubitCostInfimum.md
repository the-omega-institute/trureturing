# Actual pure-qubit cost infimum

## Abstract

The full finite affine-readout pure-qubit cost infimum has quadratic coefficient one quarter of the weighted score-square projection residual.

**Definition 1.1 (Spectral SLD information).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.spectralQFI`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.spectralQFI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In an eigenbasis of the positive semidefinite state, sum twice the squared modulus of each derivative entry divided by the sum of the corresponding eigenvalues. Terms with zero denominator are zero. Positivity on a two-sided neighborhood forces the derivative to vanish on the zero eigenspace.

**Definition 1.2 (Guarded real infimum).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.guardedInfimum`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.guardedInfimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real infimum with explicit nonempty and bounded-below guard.

**Definition 1.3 (Canonical density-state bridge).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.densityBridge`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.densityBridge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one matrix is constructed as a canonical density state, with exact equality of the recovered matrix.

**Definition 1.4 (Full actual program class).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.IsProgram`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.IsProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed finite POVM and a continuously differentiable pure state curve are defined on an open connected interval containing the closed radius interval. Born probabilities are exactly affine and positive throughout. The cost is the actual spectral SLD information at zero. No readout rank, score sign, canonical arc, or zero-score effect shape is imposed.

**Definition 1.5 (Attainable actual costs).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.costs`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.costs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set ranges over all actual programs in the preceding class.

**Definition 1.6 (Cost infimum).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.C2`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.C2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum is used only in the branch with nonempty and lower-bounded cost set. Both conditions hold at every sufficiently small positive radius.

**Definition 1.7 (Bloch vector).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.bloch`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.bloch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three real Bloch coordinates of a two by two matrix.

**Definition 1.8 (Bloch matrix).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.blochMatrix`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.blochMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hermitian matrix with a specified real trace and Bloch vector.

**Definition 1.9 (Visible readout map).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.effectReadout`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.effectReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors.

**Definition 1.10 (Orthogonal change of Bloch coordinates).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.reframe`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.reframe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An orthogonal change of the Bloch vector preserves the trace coordinate.

**Definition 1.11 (Linear Bloch map).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.blochLinear`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.blochLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch coordinates form a real linear map on complex matrices.

**Definition 1.12 (Linear change of matrix coordinates).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.reframeLinear`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.reframeLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed orthogonal Bloch frame induces a real linear map on matrices.

**Definition 1.13 (Small quadratic root).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.root`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores.

**Definition 1.14 (Radius map).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.radiusMap`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.radiusMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius includes a strict margin inside the pure-state arc and is locally inverted near zero.

**Definition 1.15 (Extended family cost).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.extendedCost`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.extendedCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost formula extends through the zero transverse parameter for the normalization branch.

**Definition 1.16 (Upper diagonal coefficient).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.upperDiag`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.upperDiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complementary quadratic root determines the upper diagonal effect coefficient.

**Definition 1.17 (Actual effect matrix).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.effect`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two diagonal coefficients and the normalized direction determine each effect matrix.

**Definition 1.18 (Pure-state arc).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.arc`

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.arc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate.

**Theorem 1.19 (Actual rank-two arc and feasible coefficients).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_rank_two_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_rank_two_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual rank-two affine readout of a pure curve admits a fixed orthonormal frame. The invisible coordinate has constant sign on the connected open interval. The effect coefficients satisfy positivity, normalization, and the exact affine-readout relations; the visible coordinate satisfies the strict radius bound.

**Theorem 1.20 (Spectral cost in the actual arc coordinates).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_cost_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_cost_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating purity identifies twice the state derivative as an SLD. Trace pairing is preserved by the orthogonal Bloch frame, giving the exact spectral cost from the visible speed and arc parameters.

**Theorem 1.21 (Normalized positive effect family).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_effect_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_effect_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any normalized centered direction, the quadratic small roots admit a differentiable normalization branch and a local inverse radius map. Along the same family the actual effects are positive semidefinite and sum to the identity, the strict arc and probability margins hold, and the extended cost has the required moment limit.

**Theorem 1.22 (Matching family of actual programs).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_upper_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_upper_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive finite probabilities and a centered direction of unit weighted second moment, the radius family gives actual POVMs and pure curves. Their spectral cost excess has the stated moment coefficient. Scaling the direction in the infimum theorem gives the original affine data.

**Theorem 1.23 (Measurement Fisher lower bound).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_fisher`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_fisher` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every differentiable positive curve with the exact affine measurement probabilities has spectral SLD information at least the classical Fisher information. Two-sided positivity first forces the derivative to vanish on the zero eigenspace, producing an SLD without invertibility. Positive residual squares then give the measurement bound.

**Theorem 1.24 (Rank alternative and binary cost gap).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_rank_alternative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_rank_alternative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual nonconstant pure-qubit readout has rank two or incurs the binary-measurement lower bound from any negative and positive score. Rank zero and rank three are excluded by the visible projection geometry.

**Theorem 1.25 (Exact quadratic infimum coefficient).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite positive probability data, a nonzero centered direction, and at least three distinct scores, the residual is positive and the normalized infimum excess tends to one quarter of that residual as real positive radii tend to zero. Repeated and zero individual scores are allowed. Cubic approximate minimizers suffice; no optimum is assumed attained. This result makes no two-score attainment or unrestricted CPTP processor equivalence claim.

The lower bound uses the joint limit of feasible rank-two coefficients: positivity, normalization, and the spectral cost equation exclude a positive limiting transverse parameter when three scores are distinct. The remaining diagonal coefficients converge to the normalized weighted score squares. An exact matching inequality then gives the quadratic lower coefficient. The rank-one branch has a fixed positive cost gap, and a smooth family of actual programs supplies the matching upper bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.C2`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.IsProgram`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_cost_transfer`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_effect_family`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_fisher`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_rank_alternative`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_rank_two_parameters`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.actual_upper_family`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.arc`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.bloch`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.blochLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.blochMatrix`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.costs`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.densityBridge`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.effect`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.effectReadout`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.extendedCost`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.guardedInfimum`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.radiusMap`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.reframe`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.reframeLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.root`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.spectralQFI`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.upperDiag`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
