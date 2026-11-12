/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonOrientation
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonOrientation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual derivative covariance under every common physical rotation. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonDerivative

/-! Coordinate correspondence for arbitrary common orientations of the actual field. -/
noncomputable section

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
open AlternatingPolygonParameters

/-- A common spatial rotation is a genuine invertible Cartesian coordinate map. -/
def orientation (N : ℕ) (θ : ℝ) : Configuration N ≃ₗ[ℝ] Configuration N where
  toFun := rotate θ
  invFun := rotate (-θ)
  map_add' v w := by ext p; cases p <;> simp [rotate] <;> ring
  map_smul' a v := by ext p; cases p <;> simp [rotate] <;> ring
  left_inv v := by
    ext p
    cases p <;> simp only [rotate, Real.cos_neg, Real.sin_neg]
    · linear_combination v (.inl _) * (Real.sin_sq_add_cos_sq θ)
    · linear_combination v (.inr _) * (Real.sin_sq_add_cos_sq θ)
  right_inv v := by
    ext p
    cases p <;> simp only [rotate, Real.cos_neg, Real.sin_neg]
    · linear_combination v (.inl _) * (Real.sin_sq_add_cos_sq θ)
    · linear_combination v (.inr _) * (Real.sin_sq_add_cos_sq θ)

/-- Differentiating the Cartesian covariance gives the actual derivative intertwining. -/
theorem derivative_rotation {N : ℕ} (b Ω θ : ℝ) {z : Configuration N}
    (hz : CollisionFree z) (v : Configuration N) :
    (jacobian N b Ω (rotate θ z)).mulVec (orientation N θ v) =
      orientation N θ ((jacobian N b Ω z).mulVec v) := by
  let e := (orientation N θ).toContinuousLinearEquiv
  have h1 := (field_differentiable_at b Ω ((collision_free_rotate θ).mpr hz)).hasFDerivAt.comp
    z e.hasFDerivAt
  have h2 := (e.hasFDerivAt (x := field N b Ω z)).comp z
    (field_differentiable_at b Ω hz).hasFDerivAt
  have heq : field N b Ω ∘ rotate θ = e ∘ field N b Ω := by
    funext w
    exact field_rotation b Ω θ w
  rw [heq] at h1
  have h := congrArg (fun L : Configuration N →L[ℝ] Configuration N => L v) (h1.unique h2)
  change fderiv ℝ (field N b Ω) (rotate θ z) (orientation N θ v) =
    orientation N θ (fderiv ℝ (field N b Ω) z v) at h
  rw [AlternatingPolygonDerivative.fderiv_eq_mulVec b Ω ((collision_free_rotate θ).mpr hz),
    AlternatingPolygonDerivative.fderiv_eq_mulVec b Ω hz] at h
  exact h

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
