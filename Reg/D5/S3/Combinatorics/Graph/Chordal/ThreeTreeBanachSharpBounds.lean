import D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
import Mathlib.Analysis.Real.Sqrt

/-! Concrete radius comparisons and finite path-power obstructions. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds

open SimpleGraph

example : (72537 / 50000 : ℝ) < 3 / 2 ∧ 3 / 2 < (Real.sqrt 17 - 1) / 2 := by
  refine ⟨by norm_num, ?_⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hn := Real.sqrt_nonneg 17
  by_contra! h
  nlinarith [mul_nonneg (show 0 ≤ 4 - Real.sqrt 17 by linarith) (show 0 ≤ 4 + Real.sqrt 17 by linarith)]

example : (4 * 2 : ℝ) / (3 * 2 + 4) = 4 / 5 := by norm_num

example : ∃ g : Fin 9 → Fin 9 → pathHexagon,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j k, (pathPowerThree 9).Adj i j → (pathPowerThree 9).Adj j k →
      (pathPowerThree 9).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
    ∀ φ : Fin 9 → pathHexagon, ∃ i j, (pathPowerThree 9).Adj i j ∧
      (3 / 4 : ℝ) < ‖g i j - (φ j - φ i)‖ := by
  obtain ⟨g, hg, ht, h⟩ := pathPowerThree_banach_lower_four_thirds 2 (by decide)
  refine ⟨g, hg, ht, fun φ => ?_⟩
  obtain ⟨i,j,hij,hl⟩ := h φ
  exact ⟨i,j,hij, (show (3/4 : ℝ) < (4*2 : ℝ)/(3*2+4) by norm_num).trans_le hl⟩

example : ∃ g : Fin 18 → Fin 18 → pathHexagon,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j k, (pathPowerThree 18).Adj i j → (pathPowerThree 18).Adj j k →
      (pathPowerThree 18).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
    ∀ φ : Fin 18 → pathHexagon, ∃ i j, (pathPowerThree 18).Adj i j ∧
      (1 : ℝ) < ‖g i j - (φ j - φ i)‖ := by
  obtain ⟨g, hg, ht, h⟩ := pathPowerThree_banach_lower_four_thirds 5 (by decide)
  refine ⟨g, hg, ht, fun φ => ?_⟩
  obtain ⟨i,j,hij,hl⟩ := h φ
  exact ⟨i,j,hij, (show (1 : ℝ) < (4*5 : ℝ)/(3*5+4) by norm_num).trans_le hl⟩

example : ∃ g : Fin 303 → Fin 303 → pathHexagon,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j k, (pathPowerThree 303).Adj i j → (pathPowerThree 303).Adj j k →
      (pathPowerThree 303).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
    ∀ φ : Fin 303 → pathHexagon, ∃ i j, (pathPowerThree 303).Adj i j ∧
      (13 / 10 : ℝ) < ‖g i j - (φ j - φ i)‖ := by
  obtain ⟨g, hg, ht, h⟩ := pathPowerThree_banach_lower_four_thirds 100 (by decide)
  refine ⟨g, hg, ht, fun φ => ?_⟩
  obtain ⟨i,j,hij,hl⟩ := h φ
  exact ⟨i,j,hij, (show (13/10 : ℝ) < (4*100 : ℝ)/(3*100+4) by norm_num).trans_le hl⟩

end Reg.D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds
