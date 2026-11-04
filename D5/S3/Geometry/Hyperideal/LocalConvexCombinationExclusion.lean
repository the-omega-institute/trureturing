/- GID: D5/S3/Geometry/Hyperideal/LocalConvexCombinationExclusion
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LocalConvexCombinationExclusion
   mirror-E: none(waiver:universal-real-inequality)
   anchors: []
   utility: none
   digest: Convexity of cosh excludes a local convex-combination flat candidate. -/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! Convexity of cosh rules out a local convex-combination candidate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.LocalConvexCombinationExclusion

private theorem cosh_convex_combination (x y lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    Real.cosh (lambda * x + (1 - lambda) * y) ≤
      lambda * Real.cosh x + (1 - lambda) * Real.cosh y := by
  have hmu0 : 0 ≤ 1 - lambda := by linarith
  have hsum : lambda + (1 - lambda) = (1 : ℝ) := by ring
  have hexp := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y)
    hlambda0 hmu0 hsum
  have hneg := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (-y))
    hlambda0 hmu0 hsum
  have hexp' : Real.exp (lambda * x + (1 - lambda) * y) ≤
      lambda * Real.exp x + (1 - lambda) * Real.exp y := by
    simpa [smul_eq_mul] using hexp
  have hneg' : Real.exp (lambda * (-x) + (1 - lambda) * (-y)) ≤
      lambda * Real.exp (-x) + (1 - lambda) * Real.exp (-y) := by
    simpa [smul_eq_mul] using hneg
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq]
  have hnegarg : -(lambda * x + (1 - lambda) * y) = lambda * (-x) + (1 - lambda) * (-y) := by ring
  rw [hnegarg]
  have hsumexp :
      lambda * Real.exp x + (1 - lambda) * Real.exp y +
          (lambda * Real.exp (-x) + (1 - lambda) * Real.exp (-y)) =
        2 * (lambda * ((Real.exp x + Real.exp (-x)) / 2) +
          (1 - lambda) * ((Real.exp y + Real.exp (-y)) / 2)) := by ring
  calc
    (Real.exp (lambda * x + (1 - lambda) * y) +
        Real.exp (lambda * (-x) + (1 - lambda) * (-y))) / 2 ≤
      (lambda * Real.exp x + (1 - lambda) * Real.exp y +
        (lambda * Real.exp (-x) + (1 - lambda) * Real.exp (-y))) / 2 := by
          apply div_le_div_of_nonneg_right (add_le_add hexp' hneg')
          norm_num
    _ = lambda * ((Real.exp x + Real.exp (-x)) / 2) +
          (1 - lambda) * ((Real.exp y + Real.exp (-y)) / 2) := by
          rw [hsumexp]
          ring

theorem local_convex_combination_exclusion
    {n : ℕ} (q q₁ q₂ : Fin n → ℝ) (ell : Fin n → ℝ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hread : q = lambda • q₁ + (1 - lambda) • q₂)
    (hpg : 1 + Real.cosh (q₁ ⬝ᵥ ell) + Real.cosh (q₂ ⬝ᵥ ell) ≤
      Real.cosh (q ⬝ᵥ ell)) : False := by
  have hdot : q ⬝ᵥ ell = lambda * (q₁ ⬝ᵥ ell) + (1 - lambda) * (q₂ ⬝ᵥ ell) := by
    rw [hread]
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [add_mul, mul_assoc]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
  have hconv := cosh_convex_combination (q₁ ⬝ᵥ ell) (q₂ ⬝ᵥ ell) lambda hlambda0 hlambda1
  rw [hdot] at hpg
  have hpos₁ : 0 < Real.cosh (q₁ ⬝ᵥ ell) := Real.cosh_pos _
  have hpos₂ : 0 < Real.cosh (q₂ ⬝ᵥ ell) := Real.cosh_pos _
  have hmu0 : 0 ≤ 1 - lambda := by linarith
  have hmu1 : 1 - lambda ≤ 1 := by linarith
  have hweight₁ : lambda * Real.cosh (q₁ ⬝ᵥ ell) ≤ Real.cosh (q₁ ⬝ᵥ ell) := by
    exact mul_le_of_le_one_left hpos₁.le hlambda1
  have hweight₂ : (1 - lambda) * Real.cosh (q₂ ⬝ᵥ ell) ≤
      Real.cosh (q₂ ⬝ᵥ ell) := by
    exact mul_le_of_le_one_left hpos₂.le hmu1
  linarith

end D5.S3.Geometry.Hyperideal.LocalConvexCombinationExclusion
