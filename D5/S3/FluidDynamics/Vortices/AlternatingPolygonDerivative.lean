/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Cartesian partial-derivative matrix represents the actual Frechet derivative. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The genuine derivative and its Cartesian matrix representation. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonDerivative
open AlternatingPolygonParameters

/-- Every reported matrix entry is a coordinate of the genuine derivative. -/
theorem jacobian_entry {N : ℕ} (b Ω : ℝ) {z : Configuration N}
    (hz : CollisionFree z) (p q : Fin N ⊕ Fin N) :
    jacobian N b Ω z p q =
      (fderiv ℝ (field N b Ω) z (Pi.single q 1)) p := by
  classical
  have ht : HasDerivAt (fun t : ℝ => z + t • Pi.single q (1 : ℝ))
      (Pi.single q 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single q (1 : ℝ))).const_add z
  have h := (field_differentiable_at b Ω hz).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) ht (by simp)
  exact ((hasDerivAt_pi.mp h) p).deriv

/-- The full derivative acts by the actual Cartesian Jacobian on every direction. -/
theorem fderiv_eq_mulVec {N : ℕ} (b Ω : ℝ) {z : Configuration N}
    (hz : CollisionFree z) (v : Configuration N) :
    fderiv ℝ (field N b Ω) z v = (jacobian N b Ω z).mulVec v := by
  classical
  have hv : v = ∑ q, v q • Pi.single q (1 : ℝ) := by
    ext p
    simp [Pi.single_apply]
  ext p
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ q, v q * (fderiv ℝ (field N b Ω) z (Pi.single q 1)) p) =
    ∑ q, jacobian N b Ω z p q * v q
  apply Finset.sum_congr rfl
  intro q _
  rw [jacobian_entry b Ω hz]
  ring

/-- A kernel-checked Frechet derivative, with no spectral or matrix assumption. -/
theorem hasFDerivAt_field {N : ℕ} (b Ω : ℝ) {z : Configuration N}
    (hz : CollisionFree z) :
    HasFDerivAt (field N b Ω)
      ((jacobian N b Ω z).toLin'.toContinuousLinearMap) z := by
  convert (field_differentiable_at b Ω hz).hasFDerivAt using 1
  ext v p
  exact congrFun (fderiv_eq_mulVec b Ω hz v).symm p

/-- The canonical normalized matrix is the matrix of this same genuine derivative. -/
theorem hasFDerivAt_normalized (N : ℕ) :
    HasFDerivAt (AlternatingPolygonSpectrum.field N)
      ((AlternatingPolygonSpectrum.jacobian N).toLin'.toContinuousLinearMap)
      (AlternatingPolygonSpectrum.polygon N) := by
  have h := hasFDerivAt_field 2 (1 / 2) (polygon_collision_free N)
  have hJ : AlternatingPolygonParameters.jacobian N 2 (1 / 2)
      (AlternatingPolygonSpectrum.polygon N) = AlternatingPolygonSpectrum.jacobian N := by
    ext p q
    unfold AlternatingPolygonParameters.jacobian AlternatingPolygonSpectrum.jacobian
    rw [normalized_field]
  rw [hJ, normalized_field] at h
  exact h

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonDerivative
