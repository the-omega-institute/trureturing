/- GID: D5/S1/Digit/Infinite/SevenCycleCollisionData
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleCollisionData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seven-phase actual sources and the subcritical collision budget. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCollisionData

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization

/-- The two actual addresses repeat the windows 3,3,5,5,3,2,2 and 0,3,5,5,3,2,2. -/
def source (firstThree : Bool) : LegalDigits :=
  ⟨fun j => decide ((j % 21 = 1 ∧ firstThree = true) ∨ j % 21 = 4 ∨
    j % 21 = 8 ∨ j % 21 = 11 ∨ j % 21 = 13 ∨ j % 21 = 15 ∨ j % 21 = 18), by
    intro j
    simp only [decide_eq_true_eq]
    omega⟩

/-- The seven guard states along either source. -/
def phaseGuard (j : Fin 7) : Bool := decide (j.val = 3 ∨ j.val = 4)

/-- The first source's return labels. -/
def firstLabel (j : Fin 7) : Label :=
  match j.val with
  | 0 | 1 | 4 => threeLabel
  | 2 | 3 => fiveLabel
  | _ => twoLabel

/-- The rival differs only at the first window. -/
def rivalLabel (j : Fin 7) : Label :=
  if j.val = 0 then nullLabel else firstLabel j

/-- The seven shared colors, including the first color one. -/
def phaseColor (j : Fin 7) : Fin 6 :=
  match j.val with
  | 0 => 1
  | 1 | 4 => 0
  | 2 => 2
  | 3 | 5 => 3
  | _ => 4

/-- The lower critical first-entry coordinate. -/
noncomputable def lowerEntry : ℝ := 3 * (g - 1) / 5
/-- The upper critical first-entry coordinate. -/
noncomputable def upperEntry : ℝ := (11 * g - 1) / 10
/-- The center used by the common six-window suffix. -/
noncomputable def referenceTail : ℝ := (-4 + t) / 5
/-- The suffix's terminal reference coordinate. -/
noncomputable def referenceEnd : ℝ := t / 5
/-- The strict budget reduction. -/
noncomputable def reduction : ℝ := g ^ 7 * (g - 1 / 5) / (4 * (1 + g ^ 7))
/-- A positive budget strictly smaller than the critical radius. -/
noncomputable def budget : ℝ := lambda - reduction
/-- The first phase's coordinate for the first source. -/
noncomputable def firstEntry : ℝ :=
  lowerEntry + g ^ 7 * (referenceEnd - lowerEntry) / (1 + g ^ 7)
/-- The first phase's coordinate for the rival. -/
noncomputable def rivalEntry : ℝ := upperEntry - 4 * reduction
/-- The zero-label feeding head sharing the first source's literal tail. -/
noncomputable def feedingEntry : ℝ :=
  upperEntry + g ^ 7 * (referenceEnd - lowerEntry) / (1 + g ^ 7)

/-- Suffix coordinates, built with the original branch maps. -/
noncomputable def phase (z : ℝ) (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => z
  | 1 => branch threeLabel (branch fiveLabel (branch fiveLabel
      (branch threeLabel (branch twoLabel (branch twoLabel z)))))
  | 2 => branch fiveLabel (branch fiveLabel
      (branch threeLabel (branch twoLabel (branch twoLabel z))))
  | 3 => branch fiveLabel (branch threeLabel (branch twoLabel (branch twoLabel z)))
  | 4 => branch threeLabel (branch twoLabel (branch twoLabel z))
  | 5 => branch twoLabel (branch twoLabel z)
  | _ => branch twoLabel z

private theorem golden_data :
    t ^ 2 + t = 1 ∧ g = 2 * t - 1 ∧ g ^ 2 + 4 * g = 1 ∧
      (4 / 17 : ℝ) < g ∧ g < 1 / 4 := by
  have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have ht2 : t ^ 2 + t = 1 := by
    change (Real.goldenRatio⁻¹) ^ 2 + Real.goldenRatio⁻¹ = 1
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hg : g = 2 * t - 1 := by
    dsimp [g]
    nlinarith [congrArg (fun x : ℝ => t * x) ht2]
  have hg2 : g ^ 2 + 4 * g = 1 := by rw [hg]; nlinarith [ht2]
  have hg0 : 0 < g := pow_pos ht 3
  refine ⟨ht2, hg, hg2, ?_, ?_⟩
  · by_contra hn
    have hn : g ≤ 4 / 17 := le_of_not_gt hn
    nlinarith [mul_nonneg hg0.le (sub_nonneg.mpr hn)]
  · nlinarith [sq_nonneg (g - 1 / 4)]

private theorem source_period (b : Bool) : bitShift (source b) 21 = source b := by
  apply Subtype.ext
  funext j
  simp [bitShift, source, Nat.add_mod]

private theorem source_windows (b : Bool) (j : ℕ) :
    window (source b) j =
      if b then firstLabel ⟨j % 7, Nat.mod_lt _ (by decide)⟩
      else rivalLabel ⟨j % 7, Nat.mod_lt _ (by decide)⟩ := by
  have hm0 : 3 * j % 21 = 3 * (j % 7) := by omega
  have hm1 : (1 + 3 * j) % 21 = 1 + 3 * (j % 7) := by omega
  have hm2 : (2 + 3 * j) % 21 = 2 + 3 * (j % 7) := by omega
  have hr : j % 7 < 7 := Nat.mod_lt _ (by decide)
  apply Subtype.ext
  funext i
  fin_cases i <;> cases b <;>
    simp only [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift,
      source, Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Nat.zero_add, hm0, hm1, hm2]
  all_goals rcases (show j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨
      j % 7 = 4 ∨ j % 7 = 5 ∨ j % 7 = 6 by omega) with hj | hj | hj | hj | hj | hj | hj
  all_goals simp [hj, firstLabel, rivalLabel, nullLabel, threeLabel, twoLabel, fiveLabel]
  all_goals omega

private theorem budget_bounds : 0 < reduction ∧ reduction < 1 / 20480 ∧
    0 < budget ∧ budget < lambda := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  have hg0 : 0 < g := by linarith
  have ha0 : 0 < g ^ 7 := pow_pos hg0 _
  have ha : g ^ 7 < (1 / 4 : ℝ) ^ 7 := pow_lt_pow_left₀ hghi hg0.le (by decide)
  have hep : 0 < g - 1 / 5 := by linarith
  have hD : 0 < 1 + g ^ 7 := by positivity
  have hd0 : 0 < reduction := by unfold reduction; positivity
  have hd : reduction < 1 / 20480 := by
    unfold reduction
    apply (div_lt_iff₀ (by positivity : 0 < 4 * (1 + g ^ 7))).2
    have hm := mul_lt_mul_of_pos_left (show g - 1 / 5 < 1 / 20 by linarith) ha0
    norm_num at ha
    nlinarith
  have hlam : (3 / 80 : ℝ) < lambda := by
    unfold lambda
    nlinarith
  refine ⟨hd0, hd, ?_, ?_⟩ <;> unfold budget <;> linarith

private theorem suffix_identity (z : ℝ) :
    phase z 1 = referenceTail + g ^ 6 * (z - referenceEnd) := by
  obtain ⟨ht2, hg, hg2, _, _⟩ := golden_data
  have ht : t = (1 + g) / 2 := by linarith
  have htsq : t ^ 2 = (1 - g) / 2 := by linarith
  simp [phase, branch, offset, threeLabel, fiveLabel, twoLabel,
    referenceTail, referenceEnd]
  rw [htsq, ht]
  linear_combination
    (-1 / 5 + 3 / 10 * g + 3 / 10 * g ^ 3 - 3 / 10 * g ^ 4 +
      1 / 10 * g ^ 5) * hg2

private theorem entry_fixed (b : Bool) :
    (if b then firstEntry else rivalEntry) =
      branch (if b then threeLabel else nullLabel)
        (phase (if b then firstEntry else rivalEntry) 1) := by
  obtain ⟨ht2, hg, hg2, hglo, _⟩ := golden_data
  have hg0 : 0 < g := by linarith
  have hD : 1 + g ^ 7 ≠ 0 := by positivity
  have h3 : branch threeLabel referenceTail = lowerEntry := by
    simp [branch, offset, threeLabel, referenceTail, lowerEntry]
    nlinarith
  have h0 : branch nullLabel referenceTail = upperEntry := by
    simp [branch, offset, nullLabel, referenceTail, upperEntry]
    nlinarith
  have hlin (l : Label) (z : ℝ) :
      branch l (referenceTail + g ^ 6 * (z - referenceEnd)) =
        branch l referenceTail - g ^ 7 * (z - referenceEnd) := by
    simp only [branch]
    ring
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [suffix_identity, hlin, h0]
    have he : upperEntry - referenceEnd = g - 1 / 5 := by
      unfold upperEntry referenceEnd
      linarith
    have hr : 4 * reduction = g ^ 7 * (upperEntry - referenceEnd) / (1 + g ^ 7) := by
      rw [he]
      unfold reduction
      field_simp [hD] <;> ring
    simp only [rivalEntry, hr]
    field_simp [hD] <;> ring
  · simp only [↓reduceIte]
    rw [suffix_identity, hlin, h3]
    unfold firstEntry
    field_simp [hD] <;> ring

private theorem shifted_source_windows (b : Bool) (j n : ℕ) :
    window (bitShift (source b) (3 * j)) n = window (source b) (j + n) := by
  apply Subtype.ext
  funext i
  simp [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P,
    bitShift, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem shifted_source_tail (b : Bool) (j : ℕ) :
    originalT (bitShift (source b) (3 * j)) = bitShift (source b) (3 * (j + 1)) := by
  apply Subtype.ext
  funext i
  simp [originalT, bitShift, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem source_tail_seven (b : Bool) : bitShift (source b) (3 * 7) = source b :=
  source_period b

private theorem actual_entry (b : Bool) :
    kappa (source b) = if b then firstEntry else rivalEntry := by
  let v (j : ℕ) := kappa (bitShift (source b) (3 * j))
  have hrec (j : ℕ) :
      v j = branch (window (source b) j) (v (j + 1)) := by
    have h := closed_observation_graph_realization.2.2.1
      (bitShift (source b) (3 * j))
    simpa only [v, shifted_source_windows, Nat.add_zero, shifted_source_tail] using h.1
  have h7 : v 7 = v 0 := by
    change kappa (bitShift (source b) 21) = kappa (bitShift (source b) 0)
    rw [source_period]
    rfl
  have hfix : v 0 = branch (if b then threeLabel else nullLabel) (phase (v 0) 1) := by
    conv_lhs => rw [hrec 0, hrec 1, hrec 2, hrec 3, hrec 4, hrec 5, hrec 6, h7]
    simp [source_windows, firstLabel, rivalLabel, phase]
  have hg0 : 0 < g := by have := golden_data.2.2.2.1; linarith
  have hinj (x y : ℝ)
      (hx : x = branch (if b then threeLabel else nullLabel) (phase x 1))
      (hy : y = branch (if b then threeLabel else nullLabel) (phase y 1)) : x = y := by
    rw [suffix_identity] at hx hy
    simp only [branch] at hx hy
    have hn : 1 + g ^ 7 ≠ 0 := by positivity
    apply (mul_right_cancel₀ hn)
    nlinarith [hx, hy]
  exact hinj _ _ hfix (entry_fixed b)

end D5.S1.Digit.Infinite.SevenCycleCollisionData

