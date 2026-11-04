/- GID: D5/S3/Geometry/Hyperideal/LengthGramDualMetric
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramDualMetric
   mirror-E: none(waiver:dual-metric)
   anchors: []
   utility: none
   digest: Inverse-Gram dual metric for realizing rows. -/

import D5.S3.Geometry.Hyperideal.LengthGramDualPairing
import Mathlib.Tactic

/-! The Lorentz pairing of two inverse-Gram dual vectors is the corresponding inverse-Gram entry. -/

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramDualPairing
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramDualMetric

theorem dual_metric
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j,
      lorentz (M i) (M j) = lengthGram l i j)
    (hdet : (lengthGram l).det < 0) (i j : Fin 4) :
    lorentz (dualVector (lengthGram l) M i)
      (dualVector (lengthGram l) M j) = (lengthGram l)⁻¹ i j := by
  have hcomm (x y : Fin 4 → ℝ) : lorentz x y = lorentz y x := by
    unfold lorentz
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlinear (a : Fin 4 → ℝ) (r : Fin 4) :
      lorentz (dualVector (lengthGram l) M r) a =
        ∑ k, (lengthGram l)⁻¹ r k * lorentz (M k) a := by
    unfold dualVector lorentz
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    lorentz (dualVector (lengthGram l) M i)
        (dualVector (lengthGram l) M j) =
        ∑ k, (lengthGram l)⁻¹ i k *
          lorentz (M k) (dualVector (lengthGram l) M j) :=
      hlinear (dualVector (lengthGram l) M j) i
    _ = ∑ k, (lengthGram l)⁻¹ i k *
          lorentz (dualVector (lengthGram l) M j) (M k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hcomm]
    _ = ∑ k, (lengthGram l)⁻¹ i k * (if j = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [dual_pairing l M hM hdet j k]
    _ = (lengthGram l)⁻¹ i j := by simp

#print axioms dual_metric
end D5.S3.Geometry.Hyperideal.LengthGramDualMetric
