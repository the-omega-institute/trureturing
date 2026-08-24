/- GID: D5/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ZetaThermalStatePinchingFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite zeta weights form a diagonal thermal state fixed by basis pinching. -/

import D5.S3.Quantum.Measurement.BasisMeasurementProjection

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'zeta_thermal_state_pinching_fixed' D5 Golden/Frozen/accepted`
     returned no matches.
   * Repository searches for `zetaThermal`, `thermalState`, `pinch`, and `dephas` found
     entropy-pinching modules and the public `basis_measurement_is_orthogonal_projection`,
     but no finite zeta thermal state or fixed-point characterization. Private hits in
     `BasisMeasurementProjection` prove projector, idempotence, and expansion lemmas; they
     are not reusable, while its public orthogonal-projection theorem is reused below.
   * The only module in the target directory is `BasisMeasurementProjection`; its digest
     states the projection theorem but does not cover fixed points or zeta weights.
   * Pinned Mathlib contains the exact fixed-point characterization
     `Submodule.starProjection_eq_self_iff`; it is applied after the public upstream theorem
     identifies basis measurement with the star projection onto its exact range. -/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.ZetaThermalStatePinchingFixed

open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.RankOneContextCommutator

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

variable {d : Nat} [NeZero d]

/-- The finite partition sum of the zeta weights `(n + 1) ^ (-s)`. -/
def zetaPartition (s : ℝ) (S : Finset (Fin d)) : ℝ :=
  ∑ n ∈ S, ((n.val + 1 : Nat) : ℝ) ^ (-s)

/-- The finite zeta thermal state in context `B`, with each selected basis projector
weighted by `(n + 1) ^ (-s)` and divided by the finite partition sum. -/
def zetaThermalState (B : RankOneContext d) (s : ℝ)
    (S : Finset (Fin d)) : HermitianSpace d :=
  ∑ n ∈ S,
    (((n.val + 1 : Nat) : ℝ) ^ (-s) / zetaPartition s S) • basisProjector B n

omit [NeZero d] in
/-- Basis pinching fixes precisely the Hermitian matrices diagonal in its measured basis. -/
theorem basis_measurement_eq_self_iff (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) (A : HermitianSpace d) :
    basisMeasurement B A = A ↔ A ∈ diagonalSubspace B := by
  have hProjection := (basis_measurement_is_orthogonal_projection B hB).1
  have hRange := (basis_measurement_is_orthogonal_projection B hB).2.1
  rcases LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hProjection with
    ⟨hRangeProjection, hEq⟩
  letI : (LinearMap.range (basisMeasurement B)).HasOrthogonalProjection := hRangeProjection
  rw [hEq]
  change (LinearMap.range (basisMeasurement B)).starProjection A = A ↔
    A ∈ diagonalSubspace B
  rw [Submodule.starProjection_eq_self_iff, hRange]

omit [NeZero d] in
/-- A finite zeta thermal state belongs to the diagonal subspace of its defining context. -/
theorem zeta_thermal_state_mem_diagonal (B : RankOneContext d) (s : ℝ)
    (S : Finset (Fin d)) :
    zetaThermalState B s S ∈ diagonalSubspace B := by
  apply Submodule.sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self n))

omit [NeZero d] in
/-- Pinching in the defining basis leaves the finite zeta thermal state unchanged. -/
theorem zeta_thermal_state_pinching_fixed (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) (s : ℝ) (S : Finset (Fin d)) :
    basisMeasurement B (zetaThermalState B s S) = zetaThermalState B s S := by
  exact (basis_measurement_eq_self_iff B hB _).2
    (zeta_thermal_state_mem_diagonal B s S)

example : ∃ B : RankOneContext 1, IsRecordMeasurement B.projector ∧
    basisMeasurement B (zetaThermalState B 2 Finset.univ) =
      zetaThermalState B 2 Finset.univ := by
  let B : RankOneContext 1 :=
    { projector := fun _ => 1
      rankOne := by
        intro j
        refine ⟨by simp, by simp, by simp, ?_⟩
        intro X
        ext i k
        fin_cases i
        fin_cases k
        simp [Matrix.trace, Matrix.mul_apply]
      resolvesIdentity := by simp }
  have hB : IsRecordMeasurement B.projector := by
    refine ⟨?_, ?_, ?_, B.resolvesIdentity⟩
    · intro j
      simpa only [Matrix.star_eq_conjTranspose] using (B.rankOne j).1
    · intro j
      exact (B.rankOne j).2.1
    · intro j k hjk
      exact (hjk (Subsingleton.elim j k)).elim
  exact ⟨B, hB, zeta_thermal_state_pinching_fixed B hB 2 Finset.univ⟩

#print axioms zeta_thermal_state_pinching_fixed

end D5.S3.Quantum.Measurement.ZetaThermalStatePinchingFixed
