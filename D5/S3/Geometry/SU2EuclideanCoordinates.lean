/- GID: D5/S3/Geometry/SU2EuclideanCoordinates
   generality: G
   mirror-B: none(waiver:covered-by-su2-tangent-lower-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Isometric Euclidean-three embedding and contractive imaginary projection. -/

import D5.S3.Geometry.SU2TangentGeometry

/-! Omega original.

Isometric Euclidean-three embedding and contractive imaginary projection. -/

noncomputable section
open scoped Quaternion InnerProductSpace
namespace SimpleGraph.SU2Tangent

abbrev R3 := EuclideanSpace ℝ (Fin 3)

def toQuat : R3 →ₗ[ℝ] ℍ[ℝ] where
  toFun x := ⟨0, x 0, x 1, x 2⟩
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

def fromQuat : ℍ[ℝ] →ₗ[ℝ] R3 where
  toFun x := WithLp.toLp 2 ![x.imI, x.imJ, x.imK]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

@[simp] theorem from_to (x : R3) : fromQuat (toQuat x) = x := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem toQuat_re (x : R3) : (toQuat x).re = 0 := rfl

theorem fromQuat_norm_le (x : ℍ[ℝ]) : ‖fromQuat x‖ ≤ ‖x‖ := by
  have hx := Quaternion.normSq_eq_norm_mul_self x
  rw [Quaternion.normSq_def'] at hx
  have hv : ‖fromQuat x‖ ^ 2 = x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [fromQuat, Fin.sum_univ_three]
  nlinarith [sq_nonneg x.re, norm_nonneg x, norm_nonneg (fromQuat x)]

theorem toQuat_norm (x : R3) : ‖toQuat x‖ = ‖x‖ := by
  have he : Quaternion.normSq (toQuat x) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Quaternion.normSq_def', toQuat, Fin.sum_univ_three]
  rw [Quaternion.normSq_eq_norm_mul_self] at he
  nlinarith [norm_nonneg x, norm_nonneg (toQuat x)]

end SimpleGraph.SU2Tangent
