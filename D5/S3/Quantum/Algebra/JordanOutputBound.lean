/- GID: D5/S3/Quantum/Algebra/JordanOutputBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/JordanOutputBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic]
   utility: none
   digest: Square-controlled Jordan derivations have the actual-output square-root-three bound. -/

import Mathlib.Algebra.Jordan.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.JordanOutputBound

variable {E : Type*} [NonUnitalNonAssocCommRing E]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A derivation whose square is the associator operator is bounded without
assuming that the underlying normed space is complete. -/
theorem norm_derivation_le
    (hnorm : ∀ x y : E, ‖x * y‖ ≤ ‖x‖ * ‖y‖)
    (hsq : ∀ x : E, ‖x * x‖ = ‖x‖ ^ 2)
    (δ : E →ₗ[ℝ] E) (q : E)
    (hder : ∀ x y, δ (x * y) = δ x * y + x * δ y)
    (hdelta : ∀ x, δ (δ x) = q * (q * x) - (q * q) * x)
    (b : E) : ‖δ b‖ ≤ Real.sqrt 3 * ‖q‖ * ‖b‖ := by
  have hH (x : E) : ‖δ (δ x)‖ ≤ 2 * ‖q‖ ^ 2 * ‖x‖ := by
    rw [hdelta]
    calc
      ‖q * (q * x) - (q * q) * x‖ ≤ ‖q * (q * x)‖ + ‖(q * q) * x‖ := norm_sub_le _ _
      _ ≤ ‖q‖ * (‖q‖ * ‖x‖) + ‖q‖ ^ 2 * ‖x‖ := by
        exact add_le_add ((hnorm _ _).trans
          (mul_le_mul_of_nonneg_left (hnorm _ _) (norm_nonneg _)))
          (by simpa only [hsq] using hnorm (q * q) x)
      _ = 2 * ‖q‖ ^ 2 * ‖x‖ := by ring
  have htwice : δ (δ (b * b)) =
      (δ (δ b) * b + b * δ (δ b)) + (δ b * δ b + δ b * δ b) := by
    rw [hder, map_add, hder, hder]
    abel
  have hid : δ b * δ b + δ b * δ b =
      δ (δ (b * b)) - (δ (δ b) * b + b * δ (δ b)) := by
    rw [htwice]
    abel
  have htwo : 2 * ‖δ b‖ ^ 2 ≤ 6 * ‖q‖ ^ 2 * ‖b‖ ^ 2 := by
    calc
      2 * ‖δ b‖ ^ 2 = ‖δ b * δ b + δ b * δ b‖ := by
        rw [← two_smul ℝ, norm_smul, hsq]
        norm_num
      _ ≤ ‖δ (δ (b * b))‖ + ‖δ (δ b) * b + b * δ (δ b)‖ := by
        rw [hid]
        exact norm_sub_le _ _
      _ ≤ 2 * ‖q‖ ^ 2 * ‖b * b‖ +
          (‖δ (δ b) * b‖ + ‖b * δ (δ b)‖) :=
        add_le_add (hH _) (norm_add_le _ _)
      _ ≤ 2 * ‖q‖ ^ 2 * ‖b‖ ^ 2 +
          ((2 * ‖q‖ ^ 2 * ‖b‖) * ‖b‖ + ‖b‖ * (2 * ‖q‖ ^ 2 * ‖b‖)) := by
        rw [hsq]
        exact add_le_add le_rfl (add_le_add
          ((hnorm _ _).trans (mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _)))
          ((hnorm _ _).trans (mul_le_mul_of_nonneg_left (hH _) (norm_nonneg _))))
      _ = 6 * ‖q‖ ^ 2 * ‖b‖ ^ 2 := by ring
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 3 * ‖q‖ * ‖b‖ := by positivity
  nlinarith [sq_nonneg (‖δ b‖ + Real.sqrt 3 * ‖q‖ * ‖b‖),
    sq_nonneg (‖δ b‖ - Real.sqrt 3 * ‖q‖ * ‖b‖)]

end D5.S3.Quantum.Algebra.JordanOutputBound
