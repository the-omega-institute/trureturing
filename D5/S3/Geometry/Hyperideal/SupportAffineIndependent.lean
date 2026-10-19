/- GID: D5/S3/Geometry/Hyperideal/SupportAffineIndependent
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SupportAffineIndependent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Lemmas]
   utility: none
   digest: Two independent support traces and a separating pair force four points to be affinely independent. -/

import D5.S3.Geometry.Hyperideal.LengthGramPolytope
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.SupportAffineIndependent

abbrev V := Fin 4 → ℝ

/-- Two linear supports triangularize a four-point affine relation. -/
theorem support_affine_independent (v : Fin 4 → V)
    (L M : V →ₗ[ℝ] ℝ) (hL0 : L (v 0) ≠ 0)
    (hL : ∀ j : Fin 3, L (v j.succ) = 0)
    (hM1 : M (v 1) ≠ 0) (hM2 : M (v 2) = 0) (hM3 : M (v 3) = 0)
    (h23 : v 2 ≠ v 3) : AffineIndependent ℝ v := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw he j
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hw] at he
  have h0 : w 0 = 0 := by
    have hh := congrArg L he
    simp [Fin.sum_univ_succ] at hh
    have h1 := hL 0
    have h2 := hL 1
    have h3 := hL 2
    change L (v 1) = 0 at h1
    change L (v 2) = 0 at h2
    change L (v 3) = 0 at h3
    simp [h1, h2, h3] at hh
    exact hh.resolve_right hL0
  have h1 : w 1 = 0 := by
    have hh := congrArg M he
    simp [Fin.sum_univ_succ, h0, hM2, hM3] at hh
    exact hh.resolve_right hM1
  have h3 : w 3 = -w 2 := by
    simp [Fin.sum_univ_succ, h0, h1] at hw
    linarith
  have hz : w 2 • (v 2 - v 3) = 0 := by
    have hz' : w 2 • v 2 + -(w 2 • v 3) = 0 := by
      simpa [Fin.sum_univ_succ, h0, h1, h3] using he
    rw [smul_sub, sub_eq_add_neg]
    exact hz'
  have h2 : w 2 = 0 := (smul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h23)
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · simpa [h2] using h3

#print axioms support_affine_independent

end D5.S3.Geometry.Hyperideal.SupportAffineIndependent
