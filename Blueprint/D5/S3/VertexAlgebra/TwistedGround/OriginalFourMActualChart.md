# Puncture assignments and lifts

## Abstract

The physical charts of the original mixed four-point kernel

The physical order is P, Q, R, S at 1, z, 0, infinity. The A, B and D native left pairs and right insertion are respectively (P,Q;R), (Q,R;P) and (P,R;Q). The detector stays at infinity. The period arguments are 1-1/z, z and 1/z.

**Theorem 1.1 (The two physical transitions).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chart_changes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chart_changes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native coordinate maps to Z=(q*x-p)/(x-1). The A-to-B and A-to-D maps preserve Z and are (z-1)/(z*x-1) and (z-1)*x/(z*x-1), respectively.

**Theorem 1.2 (The four local coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.local_coordinates_from_physical`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.local_coordinates_from_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the two left punctures take the displacements of Z evaluated at x=u and x=1/u. At the right puncture and detector first apply x -> (x-d)/(x-1). The detector uses 1/Z.

**Theorem 1.3 (Local maps and their derivatives).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.local_coordinate_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.local_coordinate_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every local map is lambda*u/(1-eta*u) with derivative lambda at zero. In physical order the derivative rows are (1-z,z-1,z,1/z), (-1,z,-z,-1) and (1,-z,-1,-1/z).

**Theorem 1.4 (Local square roots on the real overlap).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chosen_roots`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chosen_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<z<1 a negative scale takes i times the positive square root of its absolute value. The lower lip of the D period parameter gives the root i*sqrt(1-z)/sqrt(z) of 1-r.

**Theorem 1.5 (Relative half-current signs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.half_differential_signs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.half_differential_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed local half differentials at zero compare as -i*sqrt(z) times (+,+,+,-) for A/B and i times (+,-,-,+) for A/D.

**Theorem 1.6 (Cubic lifts of both transitions).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chart_lifts`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chart_lifts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the transition derivative by the corresponding overall phase and by y gives the new cubic coordinate. This proves the differential identities away from the punctures.

**Theorem 1.7 (Spatial covariance in the new differential units).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.covariance_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.covariance_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After including the squares of the lift factors, the A-to-B difference is z*C(rA)+(1-z)/2+C(z), and the A-to-D difference is C(rA)+C(rD). Here C stands for the period correction to be supplied by the continued period.

**Theorem 1.8 (The lowering coefficient at each actual puncture).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.puncture_lowering`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.puncture_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse coordinate is u/(lambda+eta*u). The factorial-normalized powers of the original oscillatorLower with parameter -eta are the native normally ordered coefficients on any oscillator polynomial. Both left inputs and the reflected detectors therefore carry the negative lowering parameter.

**Theorem 1.9 (The free same-orientation covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.puncture_cauchy_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.puncture_cauchy_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each local map and chosen lift obeys the original free half-current Cauchy correction. The regular kernel at roots b and c is eta*(1+b*c)/(2*b*c*(b+c)^2).

**Theorem 1.10 (The mixed free covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.mixed_free_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.mixed_free_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual free entry for the in/out pair of either native leg sums to -(1+u*v)/(2*(1-u*v)^2) on the disk. In the effective covariance the same scalar is multiplied by the Gram entry.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chart_changes`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chart_lifts`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.chosen_roots`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.covariance_discrepancy`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.half_differential_signs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.local_coordinate_derivatives`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.local_coordinates_from_physical`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.mixed_free_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.puncture_cauchy_correction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart.puncture_lowering`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy](../HalfFock/OriginalHalfCurrentCauchy.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks](OriginalGaussianExternalBlocks.md)
