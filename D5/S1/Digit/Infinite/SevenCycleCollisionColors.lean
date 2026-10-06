/- GID: D5/S1/Digit/Infinite/SevenCycleCollisionColors
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCollisionColors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict color margins for the two seven-phase source orbits. -/

import D5.S1.Digit.Infinite.SevenCycleCollisionData

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCollisionColors

open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open private source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private golden_data budget_bounds from D5.S1.Digit.Infinite.SevenCycleCollisionData

private theorem entry_algebra :
    firstEntry = lowerEntry + (61 + 15 * g) * reduction ∧
    upperEntry - lowerEntry = t ∧ lambda = (1 - g) / 20 := by
  obtain ⟨ht2, hg, hg2, hglo, _⟩ := golden_data
  have hg0 : 0 < g := by linarith
  have hD : 1 + g ^ 7 ≠ 0 := by positivity
  have he : 4 * (referenceEnd - lowerEntry) = (61 + 15 * g) * (g - 1 / 5) := by
    unfold referenceEnd lowerEntry
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have he' : referenceEnd - lowerEntry = (61 + 15 * g) * (g - 1 / 5) / 4 := by
      linarith
    unfold firstEntry reduction
    rw [he']
    field_simp [hD] <;> ring
  · unfold upperEntry lowerEntry
    linarith
  · unfold lambda
    linarith

private theorem entry_bounds :
    firstEntry ∈ Set.Icc lowerEntry upperEntry ∧
    rivalEntry ∈ Set.Icc lowerEntry upperEntry ∧
    firstEntry ∈ Set.Ioo (cellLower 1 - budget) (cellUpper 1 + budget) ∧
    rivalEntry ∈ Set.Ioo (cellLower 1 - budget) (cellUpper 1 + budget) ∧
    rivalEntry ∈ Set.Ioo (cellLower 2) (cellUpper 2) ∧
    feedingEntry ∈ Set.Ioo (cellLower 2) (cellUpper 2) := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  obtain ⟨hd0, hd, hb0, hb⟩ := budget_bounds
  obtain ⟨hx, hgap, hlam⟩ := entry_algebra
  have hm0 : 0 < (61 + 15 * g) * reduction := by positivity
  have hm : (61 + 15 * g) * reduction < 1 / 256 := by
    have hf : 61 + 15 * g < 65 := by linarith
    have hmul := mul_lt_mul_of_pos_right hf hd0
    nlinarith
  have hz : feedingEntry = upperEntry + (61 + 15 * g) * reduction := by
    unfold feedingEntry
    have := hx
    unfold firstEntry at this
    linarith
  simp only [Set.mem_Icc, Set.mem_Ioo]
  norm_num [cellLower, cellUpper, cuts]
  rw [hx, hz]
  unfold rivalEntry budget lowerEntry upperEntry at *
  rw [hlam] at *
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  · constructor <;> nlinarith

private theorem uniform_phase_bounds (z : ℝ) (hz : z ∈ Set.Icc lowerEntry upperEntry) :
    phase z 1 ∈ Set.Ioo (-7 / 10) (-1 / 2) ∧
    phase z 2 ∈ Set.Ioo (1 / 5) (3 / 10) ∧
    phase z 3 ∈ Set.Ioo (1 / 2) (7 / 12) ∧
    phase z 4 ∈ Set.Ioo (-5 / 6) (-1 / 2) ∧
    phase z 5 ∈ Set.Ioo (2 / 3) (5 / 6) ∧
    phase z 6 ∈ Set.Icc ((45 * g - 1) / 10) ((4 + 30 * g) / 10) := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  have hg0 : 0 < g := by linarith
  have hzs : -1 ≤ z ∧ z ≤ 1 := by
    simp only [Set.mem_Icc] at hz
    unfold lowerEntry upperEntry at hz
    constructor <;> linarith
  let v6 := 1 - g * z
  let v5 := 1 - g * v6
  let v4 := -t - g * v5
  let v3 := t ^ 2 - g * v4
  let v2 := t ^ 2 - g * v3
  let v1 := -t - g * v2
  have h6 : (45 * g - 1) / 10 ≤ v6 ∧ v6 ≤ (4 + 30 * g) / 10 := by
    have hl := mul_nonneg hg0.le (sub_nonneg.mpr hz.1)
    have hu := mul_nonneg hg0.le (sub_nonneg.mpr hz.2)
    unfold lowerEntry at hl
    unfold upperEntry at hu
    dsimp [v6]
    constructor <;> nlinarith
  have h5 : (2 / 3 : ℝ) < v5 ∧ v5 < 5 / 6 := by
    have hl := mul_nonneg (sq_nonneg g) (show 0 ≤ z + 1 by linarith [hzs.1])
    have hu := mul_nonneg (sq_nonneg g) (show 0 ≤ 1 - z by linarith [hzs.2])
    dsimp [v5, v6]
    constructor <;> nlinarith
  have h4 : (-5 / 6 : ℝ) < v4 ∧ v4 < -1 / 2 := by
    have hl := mul_lt_mul_of_pos_left h5.1 hg0
    have hu := mul_lt_mul_of_pos_left h5.2 hg0
    dsimp [v4]
    constructor <;> nlinarith
  have h3 : (1 / 2 : ℝ) < v3 ∧ v3 < 7 / 12 := by
    have hl := mul_lt_mul_of_pos_left h4.1 hg0
    have hu := mul_lt_mul_of_pos_left h4.2 hg0
    dsimp [v3]
    constructor <;> nlinarith
  have h2 : (1 / 5 : ℝ) < v2 ∧ v2 < 3 / 10 := by
    have hl := mul_lt_mul_of_pos_left h3.1 hg0
    have hu := mul_lt_mul_of_pos_left h3.2 hg0
    dsimp [v2]
    constructor <;> nlinarith
  have h1 : (-7 / 10 : ℝ) < v1 ∧ v1 < -1 / 2 := by
    have hl := mul_lt_mul_of_pos_left h2.1 hg0
    have hu := mul_lt_mul_of_pos_left h2.2 hg0
    dsimp [v1]
    constructor <;> nlinarith
  have hv : v1 ∈ Set.Ioo (-7 / 10) (-1 / 2) ∧
      v2 ∈ Set.Ioo (1 / 5) (3 / 10) ∧ v3 ∈ Set.Ioo (1 / 2) (7 / 12) ∧
      v4 ∈ Set.Ioo (-5 / 6) (-1 / 2) ∧ v5 ∈ Set.Ioo (2 / 3) (5 / 6) ∧
      v6 ∈ Set.Icc ((45 * g - 1) / 10) ((4 + 30 * g) / 10) :=
    ⟨h1, h2, h3, h4, h5, h6⟩
  simpa [phase, branch, offset, threeLabel, fiveLabel, twoLabel,
    v1, v2, v3, v4, v5, v6] using hv

private theorem uniform_colors (z : ℝ) (hz : z ∈ Set.Icc lowerEntry upperEntry)
    (j : Fin 7) (hj : j ≠ 0) :
    phase z j ∈ Set.Ioo (cellLower (phaseColor j) - budget)
      (cellUpper (phaseColor j) + budget) := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  obtain ⟨hd0, hd, hb0, hb⟩ := budget_bounds
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := uniform_phase_bounds z hz
  have hlam := entry_algebra.2.2
  have ht : t = (1 + g) / 2 := by linarith
  have htsq : t ^ 2 = (1 - g) / 2 := by linarith
  fin_cases j
  · exact False.elim (hj rfl)
  all_goals norm_num [phase, phaseColor, cellLower, cellUpper, cuts, Set.mem_Ioo, Set.mem_Icc] at *
  all_goals simp only [budget, hlam, htsq, ht] at *
  all_goals constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, hglo, hghi, hd0, hd, hb0, htsq]

end D5.S1.Digit.Infinite.SevenCycleCollisionColors
