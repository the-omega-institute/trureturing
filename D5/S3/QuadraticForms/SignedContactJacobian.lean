/- GID: D5/S3/QuadraticForms/SignedContactJacobian
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SignedContactJacobian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Characterize the homogeneous signed contact equations by contact and tangent nullspaces. -/

import D5.S3.LinearAlgebra.Matrix.WeightedContactJacobian

/-! Exact kernel of the linearized moment and dual contact equations. -/

namespace D5.S3.QuadraticForms.SignedContactJacobian

open Matrix
open scoped Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]

/-- If the interior curvatures are nonzero and each signed weight is its
curvature times a strictly negative factor, every homogeneous solution has
zero interior motion. The other components lie in the indicated nullspaces. -/
theorem kernel_iff (contact : Matrix m n R) (tangent : Matrix m k R)
    (weight curvature factor : k → R)
    (hCurvature : ∀ i, curvature i ≠ 0) (hFactor : ∀ i, 0 < factor i)
    (hWeight : ∀ i, weight i = -(factor i * curvature i))
    (u : n → R) (y : m → R) (v : k → R) :
    (contact *ᵥ u + tangent *ᵥ (diagonal weight *ᵥ v) = 0 ∧
      contactᵀ *ᵥ y = 0 ∧ tangentᵀ *ᵥ y + diagonal curvature *ᵥ v = 0) ↔
      contact *ᵥ u = 0 ∧ contactᵀ *ᵥ y = 0 ∧ tangentᵀ *ᵥ y = 0 ∧ v = 0 := by
  constructor
  · rintro ⟨hmoment, hcontact, hstationary⟩
    have weightedMotion :
        diagonal weight *ᵥ v = diagonal factor *ᵥ (tangentᵀ *ᵥ y) := by
      funext i
      have hrow := congrFun hstationary i
      simp only [Pi.add_apply, Pi.zero_apply, mulVec_diagonal] at hrow
      have hrow' : curvature i * v i = -((tangentᵀ *ᵥ y) i) :=
        eq_neg_of_add_eq_zero_right hrow
      simp only [mulVec_diagonal, hWeight, neg_mul, mul_assoc, hrow', mul_neg, neg_neg]
    rw [weightedMotion] at hmoment
    obtain ⟨hu, hy, htangent⟩ :=
      (Omega.WeightedContactJacobian.reduced_kernel_iff contact tangent factor hFactor u y).mp
        ⟨hmoment, hcontact⟩
    rw [htangent, zero_add] at hstationary
    have hv : v = 0 := by
      funext i
      have hrow := congrFun hstationary i
      simp only [mulVec_diagonal, Pi.zero_apply] at hrow ⊢
      exact (mul_eq_zero.mp hrow).resolve_left (hCurvature i)
    exact ⟨hu, hy, htangent, hv⟩
  · rintro ⟨hmoment, hcontact, htangent, hv⟩
    exact ⟨by simp only [hmoment, hv, mulVec_zero, add_zero], hcontact,
      by simp only [htangent, hv, mulVec_zero, add_zero]⟩

end D5.S3.QuadraticForms.SignedContactJacobian
