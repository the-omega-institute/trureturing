# Finite Zeta Thermal States Are Fixed by Basis Pinching

## Abstract

Basis pinching fixes exactly the diagonal Hermitian operators and therefore fixes finite zeta thermal states in their defining basis.

**Lemma 1.1 (The fixed points of basis measurement are exactly diagonal).**

$$\forall d, B: \operatorname{RankOneContext}\left(d\right), A: \operatorname{HermitianSpace}\left(d\right), \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \Rightarrow (\operatorname{basisMeasurement}\left(B, A\right) = A \iff A \in \operatorname{diagonalSubspace}\left(B\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed.basis_measurement_eq_self_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complete rank-one record measurement, a Hermitian operator is unchanged by basis pinching exactly when it lies in the span of the measured basis projectors. Thus the diagonal subspace is the entire fixed-point space, not merely a collection of fixed points.

**Lemma 1.2 (A finite zeta thermal state is diagonal).**

$$\forall d, B: \operatorname{RankOneContext}\left(d\right), s: \mathbb{R}, S: \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right), \operatorname{zetaThermalState}\left(B, s, S\right) \in \operatorname{diagonalSubspace}\left(B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed.zeta_thermal_state_mem_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every summand of the finite zeta thermal state is a scalar multiple of one of the defining context's basis projectors. Since their span is a real subspace, the complete finite weighted sum belongs to the diagonal subspace; the common partition factor does not affect this membership.

**Theorem 1.3 (Basis pinching fixes the finite zeta thermal state).**

$$\forall d, B: \operatorname{RankOneContext}\left(d\right), s: \mathbb{R}, S: \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right), \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right) \Rightarrow \operatorname{basisMeasurement}\left(B, \operatorname{zetaThermalState}\left(B, s, S\right)\right) = \operatorname{zetaThermalState}\left(B, s, S\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed.zeta_thermal_state_pinching_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite zeta-weighted combination has no component outside the diagonal subspace of its defining context. For a complete record measurement, basis pinching is therefore the identity on this operator, so the thermal combination is left unchanged.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed.basis_measurement_eq_self_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed.zeta_thermal_state_mem_diagonal`
- Truth anchor: `D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed.zeta_thermal_state_pinching_fixed`
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](BasisMeasurementProjection.md)
