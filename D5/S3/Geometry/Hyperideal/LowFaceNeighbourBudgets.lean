/- GID: D5/S3/Geometry/Hyperideal/LowFaceNeighbourBudgets
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LowFaceNeighbourBudgets
   mirror-E: none(waiver:continuous-six-coordinate-envelope)
   anchors: []
   utility: none
   digest: Uniform low-face cosine bounds for two, three, or four short neighbours. -/

import D5.S3.Geometry.Hyperideal.CriticalTransitionStar
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.LowFaceNeighbourBudgets

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.CriticalTransitionStar

/-- At least two of the four actual neighbouring positions are short. -/
def TwoSmall (y z v w : ℝ) : Prop :=
  (y ≤ 5/4 ∧ z ≤ 5/4) ∨ (y ≤ 5/4 ∧ v ≤ 5/4) ∨
  (y ≤ 5/4 ∧ w ≤ 5/4) ∨ (z ≤ 5/4 ∧ v ≤ 5/4) ∨
  (z ≤ 5/4 ∧ w ≤ 5/4) ∨ (v ≤ 5/4 ∧ w ≤ 5/4)

/-- On the low-edge upper face, the exact six-coordinate cosine obeys
uniform bounds according to the number of short neighbouring positions. -/
theorem low_face_neighbour_budgets (y z o v w : ℝ)
    (hy : y ∈ Set.Icc 1 2) (hz : z ∈ Set.Icc 1 2)
    (ho : o ∈ Set.Icc 1 2) (hv : v ∈ Set.Icc 1 2)
    (hw : w ∈ Set.Icc 1 2) :
    (TwoSmall y z v w → cosine 2 y z o v w ≤ (70 : ℝ) / 99) ∧
    (ThreeSmall y z v w → cosine 2 y z o v w ≤ 49 * Real.sqrt 6 / 198) ∧
    ((y ≤ 5/4 ∧ z ≤ 5/4 ∧ v ≤ 5/4 ∧ w ≤ 5/4) →
      cosine 2 y z o v w ≤ (17 : ℝ) / 33) := by
  have quotient_le : ∀ (A B P q : ℝ), 0 < A → 0 < B → 0 ≤ q →
      P^2 ≤ q^2 * (A * B) → P / Real.sqrt A / Real.sqrt B ≤ q := by
    intro A B P q hA hB hq hs
    let r := Real.sqrt A * Real.sqrt B
    have hr : 0 < r := mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
    have hrsq : r^2 = A*B := by
      dsimp [r]
      rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    rw [div_div]
    change P/r ≤ q
    apply (div_le_iff₀ hr).2
    apply le_of_sq_le_sq
    · rw [mul_pow, hrsq]
      exact hs
    · exact mul_nonneg hq hr.le
  have hc1 : (1:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hc2 : (2:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hch : (5/4:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have envelope (Y Z V W q : ℝ)
      (hY : Y ∈ Set.Icc 1 2) (hZ : Z ∈ Set.Icc 1 2)
      (hV : V ∈ Set.Icc 1 2) (hW : W ∈ Set.Icc 1 2)
      (hyY : y ≤ Y) (hzZ : z ≤ Z) (hvV : v ≤ V) (hwW : w ≤ W)
      (hq : 0 ≤ q)
      (hsq : (numerator 2 Y Z 1 V W)^2 ≤
        q^2 * (rad 2 Y W * rad 2 Z V)) :
      cosine 2 y z o v w ≤ q := by
    calc
      cosine 2 y z o v w ≤ cosine 2 Y Z 1 V W :=
        cosine_mixed_comparison 2 y z o v w Y Z 1 V W
          hc2 hy hz ho hv hw hY hZ hc1 hV hW hyY hzZ ho.1 hvV hwW
      _ ≤ q := by
        unfold cosine
        exact quotient_le _ _ _ _
          (by have : (1:ℝ) ≤ Y := hY.1
              have : (1:ℝ) ≤ W := hW.1
              norm_num [rad]; nlinarith)
          (by have : (1:ℝ) ≤ Z := hZ.1
              have : (1:ℝ) ≤ V := hV.1
              norm_num [rad]; nlinarith)
          hq hsq
  have q3sq : (49 * Real.sqrt 6 / 198 : ℝ)^2 = (2401 : ℝ) / 6534 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]
    norm_num
  have q3nonneg : (0:ℝ) ≤ 49 * Real.sqrt 6 / 198 := by positivity
  constructor
  · intro hsmall
    rcases hsmall with ⟨hyb, hzb⟩ | ⟨hyb, hvb⟩ | ⟨hyb, hwb⟩ |
      ⟨hzb, hvb⟩ | ⟨hzb, hwb⟩ | ⟨hvb, hwb⟩
    · exact envelope (5/4) (5/4) 2 2 (70/99) hch hch hc2 hc2
        hyb hzb hv.2 hw.2 (by norm_num) (by norm_num [rad, numerator])
    · exact envelope (5/4) 2 (5/4) 2 (70/99) hch hc2 hch hc2
        hyb hz.2 hvb hw.2 (by norm_num) (by norm_num [rad, numerator])
    · exact envelope (5/4) 2 2 (5/4) (70/99) hch hc2 hc2 hch
        hyb hz.2 hv.2 hwb (by norm_num) (by norm_num [rad, numerator])
    · exact envelope 2 (5/4) (5/4) 2 (70/99) hc2 hch hch hc2
        hy.2 hzb hvb hw.2 (by norm_num) (by norm_num [rad, numerator])
    · exact envelope 2 (5/4) 2 (5/4) (70/99) hc2 hch hc2 hch
        hy.2 hzb hv.2 hwb (by norm_num) (by norm_num [rad, numerator])
    · exact envelope 2 2 (5/4) (5/4) (70/99) hc2 hc2 hch hch
        hy.2 hz.2 hvb hwb (by norm_num) (by norm_num [rad, numerator])
  constructor
  · intro hsmall
    rcases hsmall with ⟨hyb, hzb, hvb⟩ | ⟨hyb, hzb, hwb⟩ |
      ⟨hyb, hvb, hwb⟩ | ⟨hzb, hvb, hwb⟩
    · exact envelope (5/4) (5/4) (5/4) 2 (49 * Real.sqrt 6 / 198)
        hch hch hch hc2 hyb hzb hvb hw.2 q3nonneg
        (by rw [q3sq]; norm_num [rad, numerator])
    · exact envelope (5/4) (5/4) 2 (5/4) (49 * Real.sqrt 6 / 198)
        hch hch hc2 hch hyb hzb hv.2 hwb q3nonneg
        (by rw [q3sq]; norm_num [rad, numerator])
    · exact envelope (5/4) 2 (5/4) (5/4) (49 * Real.sqrt 6 / 198)
        hch hc2 hch hch hyb hz.2 hvb hwb q3nonneg
        (by rw [q3sq]; norm_num [rad, numerator])
    · exact envelope 2 (5/4) (5/4) (5/4) (49 * Real.sqrt 6 / 198)
        hc2 hch hch hch hy.2 hzb hvb hwb q3nonneg
        (by rw [q3sq]; norm_num [rad, numerator])
  · rintro ⟨hyb, hzb, hvb, hwb⟩
    exact envelope (5/4) (5/4) (5/4) (5/4) (17/33)
      hch hch hch hch hyb hzb hvb hwb (by norm_num)
      (by norm_num [rad, numerator])

#print axioms low_face_neighbour_budgets

end D5.S3.Geometry.Hyperideal.LowFaceNeighbourBudgets
