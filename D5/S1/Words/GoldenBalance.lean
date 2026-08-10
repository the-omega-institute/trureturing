/- GID: D5/S1/Words/GoldenBalance
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-symbolic-balance-theorem)
   anchors: []
   digest: Equal-length windows of the infinite golden word differ in true count by at most one. -/

import D5.S1.Words.GoldenWord
import D5.S1.Words.ZeckendorfBeattyBridge

namespace D5.S1.Words

/-- The number of `true` letters in the half-open golden-word window `[i, i + n)`. -/
def goldenWindowTrueCount (i n : Nat) : Nat :=
  ((Finset.range n).filter fun k => goldenWord (i + k) = true).card

private theorem golden_mechanical_letter_eq_zero_or_one (n : Nat) :
    goldenMechanicalLetter n = 0 ∨ goldenMechanicalLetter n = 1 := by
  have hslope_pos : 0 < goldenMechanicalSlope := inv_pos.mpr Real.goldenRatio_pos
  have hslope_lt_one : goldenMechanicalSlope < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hfloor : ⌊goldenMechanicalSlope⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨hslope_pos.le, hslope_lt_one⟩
  let x : Real := (n : Real) * goldenMechanicalSlope
  have hlower := Int.le_floor_add x goldenMechanicalSlope
  have hupper := Int.le_floor_add_floor x goldenMechanicalSlope
  rw [hfloor, add_zero] at hlower hupper
  have hletter : goldenMechanicalLetter n = ⌊x + goldenMechanicalSlope⌋ - ⌊x⌋ := by
    simp [goldenMechanicalLetter, x, add_mul]
  rw [hletter]
  omega

private theorem golden_word_indicator_eq_mechanical (i : Nat) :
    (if goldenWord i = true then (1 : Int) else 0) = goldenMechanicalLetter (i + 1) := by
  have hone : goldenWord i = true ↔ goldenMechanicalLetter (i + 1) = 1 :=
    (goldenWord_char_zeckendorf i).trans (zeckendorf_beatty_bridge i)
  rcases golden_mechanical_letter_eq_zero_or_one (i + 1) with hzero | hletter
  · rw [hzero]
    rw [if_neg]
    exact fun hword => by
      have h := hone.mp hword
      rw [hzero] at h
      omega
  · rw [if_pos (hone.mpr hletter), hletter]

/-- A golden-word window count is the difference of its shifted Beatty endpoints. -/
theorem goldenWindowTrueCount_eq_floor (i n : Nat) :
    (goldenWindowTrueCount i n : Int) =
      ⌊(((i + n + 1 : Nat) : Real) * Real.goldenRatio⁻¹)⌋ -
        ⌊(((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹)⌋ := by
  classical
  rw [goldenWindowTrueCount, Finset.natCast_card_filter]
  simp_rw [golden_word_indicator_eq_mechanical]
  let f : Nat → Int := fun k =>
    ⌊(((i + k + 1 : Nat) : Real) * Real.goldenRatio⁻¹)⌋
  calc
    ∑ k ∈ Finset.range n, goldenMechanicalLetter (i + k + 1) =
        ∑ k ∈ Finset.range n, (f (k + 1) - f k) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [goldenMechanicalLetter, goldenMechanicalSlope, f]
      congr 1
    _ = f n - f 0 := Finset.sum_range_sub f n
    _ = ⌊(((i + n + 1 : Nat) : Real) * Real.goldenRatio⁻¹)⌋ -
        ⌊(((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹)⌋ := by simp [f]

/-- Any two golden-word windows of the same length differ in true-letter count by at most one. -/
theorem goldenWord_balanced_one (i j n : Nat) :
    |(goldenWindowTrueCount i n : Int) - (goldenWindowTrueCount j n : Int)| ≤ 1 := by
  rw [goldenWindowTrueCount_eq_floor, goldenWindowTrueCount_eq_floor]
  let xi : Real := ((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹
  let xj : Real := ((j + 1 : Nat) : Real) * Real.goldenRatio⁻¹
  let t : Real := (n : Real) * Real.goldenRatio⁻¹
  have hi : (((i + n + 1 : Nat) : Real) * Real.goldenRatio⁻¹) = xi + t := by
    dsimp [xi, t]
    push_cast
    ring
  have hj : (((j + n + 1 : Nat) : Real) * Real.goldenRatio⁻¹) = xj + t := by
    dsimp [xj, t]
    push_cast
    ring
  have hi_lower := Int.le_floor_add xi t
  have hi_upper := Int.le_floor_add_floor xi t
  have hj_lower := Int.le_floor_add xj t
  have hj_upper := Int.le_floor_add_floor xj t
  rw [hi, hj]
  change |(⌊xi + t⌋ - ⌊xi⌋) - (⌊xj + t⌋ - ⌊xj⌋)| ≤ 1
  rw [abs_le]
  constructor <;> omega

private theorem golden_window_true_count_length_two_example :
    (List.range 6).map (fun i => goldenWindowTrueCount i 2) = [1, 1, 2, 1, 1, 1] := by
  decide

private theorem golden_window_true_count_length_five_example :
    |(goldenWindowTrueCount 0 5 : Int) - (goldenWindowTrueCount 7 5 : Int)| ≤ 1 := by
  decide

end D5.S1.Words
