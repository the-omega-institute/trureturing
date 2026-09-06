/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionChart
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The finite coordinate table is proved equivalent to the actual projective plane over F5. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionNormalizerCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

theorem axisVector_ne_zero (p : AxisChart) : axisVector p ≠ 0 := by
  fin_cases p <;> decide

set_option maxRecDepth 100000 in
private theorem nonzeroVector_chart_complete :
    ∀ v : Vector, v ≠ 0 → ∃ p : AxisChart, ∃ a : F5, a • v = axisVector p := by
  decide

def chartPoint (p : AxisChart) : ProjectiveAxis :=
  Projectivization.mk F5 (axisVector p) (axisVector_ne_zero p)

/-- The cardinality 31 is derived from the actual projective space. -/
theorem projectiveAxis_card : Nat.card ProjectiveAxis = 31 := by
  change Nat.card (Projectivization F5 Vector) = 31
  calc
    Nat.card (Projectivization F5 Vector) =
        ∑ i ∈ Finset.range 3, Nat.card F5 ^ i :=
      Projectivization.card_of_finrank F5 Vector (n := 3) (by simp [Vector])
    _ = 31 := by norm_num [F5]

private theorem chartPoint_surjective : Function.Surjective chartPoint := by
  intro x
  induction x using Projectivization.ind with
  | _ v hv =>
      obtain ⟨p, a, ha⟩ := nonzeroVector_chart_complete v hv
      refine ⟨p, ?_⟩
      apply (Projectivization.mk_eq_mk_iff' F5
        (axisVector p) v (axisVector_ne_zero p) hv).mpr
      exact ⟨a, ha⟩

private theorem chartPoint_bijective : Function.Bijective chartPoint := by
  apply (Nat.bijective_iff_surjective_and_card chartPoint).mpr
  refine ⟨chartPoint_surjective, ?_⟩
  rw [projectiveAxis_card]
  simp [AxisChart]

/-- The explicit 31-entry table is a coordinate equivalence for the actual
projective plane, not its definition. -/
noncomputable def projectiveChart : ProjectiveAxis ≃ Fin 31 :=
  (Equiv.ofBijective chartPoint chartPoint_bijective).symm

@[simp]
theorem projectiveChart_symm_apply (p : AxisChart) :
    projectiveChart.symm p = chartPoint p := by
  rfl

@[simp]
theorem projectiveChart_chartPoint (p : AxisChart) :
    projectiveChart (chartPoint p) = p := by
  rw [← projectiveChart_symm_apply, projectiveChart.apply_symm_apply]

@[simp]
theorem projectiveChart_symm_embedding_apply (p : AxisChart) :
    projectiveChart (projectiveChart.symm.toEmbedding p) = p := by
  exact projectiveChart.apply_symm_apply p

private theorem normalize_ne_zero (v : Vector) : (normalize v).1 ≠ 0 := by
  intro hv
  have hn := (normalize v).2
  simp [normalizedVectors, IsNormalized, hv] at hn

set_option maxRecDepth 100000 in
theorem normalize_scalar (v : Vector) (hv : v ≠ 0) :
    ∃ a : F5, a • v = (normalize v).1 := by
  revert v
  decide

private theorem mk_normalize (v : Vector) (hv : v ≠ 0) :
    Projectivization.mk F5 (normalize v).1 (normalize_ne_zero v) =
      Projectivization.mk F5 v hv := by
  obtain ⟨a, ha⟩ := normalize_scalar v hv
  exact (Projectivization.mk_eq_mk_iff' F5 _ _ _ _).mpr ⟨a, ha⟩

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
