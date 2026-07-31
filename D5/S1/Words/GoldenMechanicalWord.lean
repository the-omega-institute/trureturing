/- GID: D5/S1/Words/GoldenMechanicalWord
   generality: I
   mirror-B: D5/B/S1/Words/GoldenMechanicalWord
   mirror-E: none(waiver:exact-symbolic-window-criterion)
   anchors: []
   digest: A golden mechanical letter is one exactly on its fractional-coordinate window. -/

import D5.S1.Phase.Basic
import D5.S1.Dynamics.GoldenFractionalPart

namespace D5.S1.Words

open D5.S1.Phase
open D5.S1.Dynamics

/-- The slope `1 / phi` of the lower golden mechanical word. -/
noncomputable def goldenMechanicalSlope : ℝ := Real.goldenRatio⁻¹

/-- The `n`th letter of the lower golden mechanical word as a floor difference. -/
noncomputable def goldenMechanicalLetter (n : ℕ) : ℤ :=
  ⌊((n + 1 : ℕ) : ℝ) * goldenMechanicalSlope⌋ -
    ⌊(n : ℝ) * goldenMechanicalSlope⌋

/-- A golden mechanical letter is one exactly when its fractional coordinate
lies in the half-open local window `[1 - 1 / phi, 1)`. -/
theorem golden_mechanical_letter_eq_one_iff (n : ℕ) :
    goldenMechanicalLetter n = 1 ↔
      goldenFractionalPart n ∈ Set.Ico (1 - goldenMechanicalSlope) 1 := by
  have hslope : goldenMechanicalSlope = Real.goldenRatio - 1 := by
    rw [goldenMechanicalSlope, Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
    ring
  have hslope_lt_one : goldenMechanicalSlope < 1 := by
    rw [hslope]
    linarith [Real.goldenRatio_lt_two]
  let x : ℝ := (n : ℝ) * goldenMechanicalSlope
  have hfract : Int.fract x = goldenFractionalPart n := by
    dsimp [x]
    rw [goldenFractionalPart, hslope, mul_sub, mul_one]
    exact Int.fract_sub_natCast ((n : ℝ) * Real.goldenRatio) n
  have hletter : goldenMechanicalLetter n =
      ⌊x + goldenMechanicalSlope⌋ - ⌊x⌋ := by
    simp [goldenMechanicalLetter, x, add_mul]
  have hfloor : ⌊x + goldenMechanicalSlope⌋ - ⌊x⌋ =
      ⌊Int.fract x + goldenMechanicalSlope⌋ := by
    have hx : (⌊x⌋ : ℝ) + (Int.fract x + goldenMechanicalSlope) =
        x + goldenMechanicalSlope := by
      calc
        (⌊x⌋ : ℝ) + (Int.fract x + goldenMechanicalSlope) =
            ((⌊x⌋ : ℝ) + Int.fract x) + goldenMechanicalSlope := by ring
        _ = x + goldenMechanicalSlope := by rw [Int.floor_add_fract]
    rw [← hx, Int.floor_intCast_add]
    omega
  rw [hletter, hfloor, Int.floor_eq_iff]
  simp only [Set.mem_Ico]
  rw [← hfract]
  constructor
  · rintro ⟨hlower, _⟩
    norm_num at hlower
    exact ⟨(sub_le_iff_le_add).2 hlower, Int.fract_lt_one _⟩
  · rintro ⟨hlower, hupper⟩
    constructor
    · norm_num
      exact (sub_le_iff_le_add).1 hlower
    · norm_num
      linarith

end D5.S1.Words
