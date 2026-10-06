/- GID: D5/S1/Digit/Infinite/SevenCycleSeparationRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleSeparationRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unconditional finite-future separation assertion for actual singleton rivals. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleCollisionData

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization

/-- The two actual addresses repeat the windows 3,3,5,5,3,2,2 and 0,3,5,5,3,2,2. -/
private def source (firstThree : Bool) : LegalDigits :=
  ⟨fun j => decide ((j % 21 = 1 ∧ firstThree = true) ∨ j % 21 = 4 ∨
    j % 21 = 8 ∨ j % 21 = 11 ∨ j % 21 = 13 ∨ j % 21 = 15 ∨ j % 21 = 18), by
    intro j
    simp only [decide_eq_true_eq]
    omega⟩

/-- The seven guard states along either source. -/
private def phaseGuard (j : Fin 7) : Bool := decide (j.val = 3 ∨ j.val = 4)

/-- The first source's return labels. -/
private def firstLabel (j : Fin 7) : Label :=
  match j.val with
  | 0 | 1 | 4 => threeLabel
  | 2 | 3 => fiveLabel
  | _ => twoLabel

/-- The rival differs only at the first window. -/
private def rivalLabel (j : Fin 7) : Label :=
  if j.val = 0 then nullLabel else firstLabel j

/-- The seven shared colors, including the first color one. -/
private def phaseColor (j : Fin 7) : Fin 6 :=
  match j.val with
  | 0 => 1
  | 1 | 4 => 0
  | 2 => 2
  | 3 | 5 => 3
  | _ => 4

/-- The lower critical first-entry coordinate. -/
private noncomputable def lowerEntry : ℝ := 3 * (g - 1) / 5
/-- The upper critical first-entry coordinate. -/
private noncomputable def upperEntry : ℝ := (11 * g - 1) / 10
/-- The center used by the common six-window suffix. -/
private noncomputable def referenceTail : ℝ := (-4 + t) / 5
/-- The suffix's terminal reference coordinate. -/
private noncomputable def referenceEnd : ℝ := t / 5
/-- The strict budget reduction. -/
private noncomputable def reduction : ℝ := g ^ 7 * (g - 1 / 5) / (4 * (1 + g ^ 7))
/-- A positive budget strictly smaller than the critical radius. -/
private noncomputable def budget : ℝ := lambda - reduction
/-- The first phase's coordinate for the first source. -/
private noncomputable def firstEntry : ℝ :=
  lowerEntry + g ^ 7 * (referenceEnd - lowerEntry) / (1 + g ^ 7)
/-- The first phase's coordinate for the rival. -/
private noncomputable def rivalEntry : ℝ := upperEntry - 4 * reduction
/-- The zero-label feeding head sharing the first source's literal tail. -/
private noncomputable def feedingEntry : ℝ :=
  upperEntry + g ^ 7 * (referenceEnd - lowerEntry) / (1 + g ^ 7)

/-- Suffix coordinates, built with the original branch maps. -/
private noncomputable def phase (z : ℝ) (j : Fin 7) : ℝ :=
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

namespace D5.S1.Digit.Infinite.SevenCycleSeparationRefutation

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase)

/-- The finite future test uses the same rival address, all original guards and all branches. -/
noncomputable def horizon (b : ℝ) (eta : LegalDigits) (r : ℕ) (s : Bool) : ℕ → Set ℝ
  | 0 => stateInterval s
  | n + 1 => {x | (∃ c : Fin 6,
      kappa (bitShift eta (3 * r)) ∈ observation b c ∧ x ∈ observation b c) ∧
      ∃ l : Label, ∃ s' : Bool, lawful s l s' ∧
        ∃ y ∈ horizon b eta (r + 1) s' n, x = branch l y}

/-- Two different first labels can use different first colors against the same rival. -/
noncomputable def entrySet (b : ℝ) (l m : Label) (c d : Fin 6) (s : Bool) : Set ℝ :=
  stateInterval s ∩ branch l ⁻¹' observation b c ∩ branch m ⁻¹' observation b d

/-- No conditioning on a shared first-color history is imposed. -/
noncomputable def separates (b : ℝ) (eta : LegalDigits) : Prop :=
  ∃ n : ℕ, ∀ (s : Bool) (l m : Label) (c d : Fin 6),
    lawful false l s → lawful false m s → l ≠ m →
    kappa eta ∈ observation b c → kappa eta ∈ observation b d →
    entrySet b l m c d s ∩ horizon b eta 1 s n = ∅

/-- Primitive period is measured in actual three-bit windows. -/
def primitiveWindowPeriod (eta : LegalDigits) (p : ℕ) : Prop :=
  0 < p ∧ Function.Periodic (window eta) p ∧
    ∀ k : ℕ, 0 < k → Function.Periodic (window eta) k → p ≤ k

/-- The rival's actual periodic orbit consists of original singleton vertices and edges. -/
def singletonRival (q : ℕ) (R : ℝ) (eta : LegalDigits) : Prop :=
  ∃ p : ℕ, Odd p ∧ primitiveWindowPeriod eta p ∧
    ∃ v : ℕ → Vertex q R,
      (∀ j, (v j).val.1 = actualGuard false eta j ∧
        piece (v j) = {kappa (bitShift eta (3 * j))}) ∧
      (∀ j, edge (v j) (window eta j) (v (j + 1))) ∧
      (∀ j, v (j + p) = v j)

/-- Every actual odd primitive singleton rival is claimed to admit unconditional finite separation. -/
def claim : Prop :=
  ∀ (b : ℝ) (q : ℕ) (R : ℝ), 0 < b → b < lambda → endpointParameters b q R →
    ∀ eta : LegalDigits, singletonRival q R eta → separates b eta

end D5.S1.Digit.Infinite.SevenCycleSeparationRefutation

namespace D5.S1.Digit.Infinite.SevenCycleCollisionColors

open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase)
open D5.S1.Digit.Infinite.SevenCycleCollisionData (golden_data budget_bounds)

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

namespace D5.S1.Digit.Infinite.SevenCycleCollisionRecords

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase)
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source_period source_windows shifted_source_windows shifted_source_tail
  actual_entry golden_data budget_bounds entry_fixed suffix_identity)
open D5.S1.Digit.Infinite.SevenCycleCollisionColors (entry_bounds uniform_colors)

private theorem actual_phase (b : Bool) (j : Fin 7) :
    kappa (bitShift (source b) (3 * j.val)) =
      phase (if b then firstEntry else rivalEntry) j := by
  let v (j : ℕ) := kappa (bitShift (source b) (3 * j))
  have hrec (j : ℕ) : v j = branch (window (source b) j) (v (j + 1)) := by
    have h := closed_observation_graph_realization.2.2.1
      (bitShift (source b) (3 * j))
    simpa only [v, shifted_source_windows, Nat.add_zero, shifted_source_tail] using h.1
  have h0 : v 0 = if b then firstEntry else rivalEntry := actual_entry b
  have h7 : v 7 = if b then firstEntry else rivalEntry := by
    change kappa (bitShift (source b) 21) = _
    rw [source_period]
    exact actual_entry b
  change v j.val = _
  fin_cases j <;>
    simp only [h0, h7, hrec 1, hrec 2, hrec 3, hrec 4, hrec 5, hrec 6] <;>
    simp [source_windows, phase, firstLabel, rivalLabel]

private theorem actual_phase_mod (b : Bool) (j : ℕ) :
    kappa (bitShift (source b) (3 * j)) =
      phase (if b then firstEntry else rivalEntry) ⟨j % 7, Nat.mod_lt _ (by decide)⟩ := by
  have hs : bitShift (source b) (3 * j) = bitShift (source b) (3 * (j % 7)) := by
    apply Subtype.ext
    funext i
    have hm : (i + 3 * j) % 21 = (i + 3 * (j % 7)) % 21 := by omega
    simp only [bitShift, source, hm]
  rw [hs]
  simpa only [Fin.val_mk] using
    actual_phase b (⟨j % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7)

private theorem actual_phase_guard (b : Bool) (j : ℕ) :
    stateAddress (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
      (bitShift (source b) (3 * j)) := by
  unfold stateAddress
  simp only [phaseGuard, decide_eq_true_eq]
  intro h
  simp only [bitShift, source, decide_eq_false_iff_not]
  omega

private theorem actual_guard (b : Bool) (j : ℕ) :
    actualGuard false (source b) j = phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩ := by
  by_cases hj : j = 0
  · subst j; rfl
  · simp only [actualGuard, hj, ↓reduceIte, source, phaseGuard, Fin.val_mk]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega

private theorem phase_state (b : Bool) (j : ℕ) :
    phase (if b then firstEntry else rivalEntry) ⟨j % 7, Nat.mod_lt _ (by decide)⟩ ∈
      stateInterval (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
  rw [← actual_phase_mod]
  rw [← closed_observation_graph_realization.2.1 _]
  exact ⟨_, actual_phase_guard b j, rfl⟩

private theorem periodic_rival : primitiveWindowPeriod (source false) 7 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro n
    simp [source_windows, Nat.add_mod]
  · intro k hk hp
    have h := hp 0
    rw [Nat.zero_add, source_windows, source_windows] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mod, rivalLabel] at h
    have hr : k % 7 < 7 := Nat.mod_lt _ (by decide)
    rcases (show k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
      k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 by omega) with he | he | he | he | he | he | he
    · omega
    all_goals norm_num [he, firstLabel] at h
    all_goals first
      | have hc := congrArg (fun l : Label => l.val 0) h
        norm_num [threeLabel, nullLabel, fiveLabel, twoLabel] at hc <;> contradiction
      | have hc := congrArg (fun l : Label => l.val 1) h
        norm_num [threeLabel, nullLabel, fiveLabel, twoLabel] at hc <;> contradiction
      | have hc := congrArg (fun l : Label => l.val 2) h
        norm_num [threeLabel, nullLabel, fiveLabel, twoLabel] at hc <;> contradiction

end D5.S1.Digit.Infinite.SevenCycleCollisionRecords

namespace D5.S1.Digit.Infinite.SevenCycleCollisionFuture

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase)
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open D5.S1.Digit.Infinite.SevenCycleCollisionData (golden_data budget_bounds entry_fixed suffix_identity source_windows
  shifted_source_tail shifted_source_windows actual_entry)
open D5.S1.Digit.Infinite.SevenCycleCollisionColors (entry_algebra entry_bounds uniform_colors)
open D5.S1.Digit.Infinite.SevenCycleCollisionRecords (actual_phase actual_phase_mod actual_phase_guard actual_guard phase_state)

private theorem phase_lawful (b : Bool) (j : ℕ) :
    lawful (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (window (source b) j)
      (phaseGuard ⟨(j + 1) % 7, Nat.mod_lt _ (by decide)⟩) := by
  have h := actual_phase_guard b j
  refine ⟨?_, ?_⟩
  · simpa [stateAddress, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using h
  · simp only [outgoing, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P,
      bitShift, source, phaseGuard, Fin.val_mk]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega

private theorem feeding_scalar : branch nullLabel (phase firstEntry 1) = feedingEntry := by
  have h := entry_fixed true
  simp only [↓reduceIte] at h
  have hg := golden_data.2.1
  have hgap := entry_algebra.2.1
  simp [branch, offset, threeLabel, nullLabel] at h ⊢
  unfold feedingEntry firstEntry at *
  linarith

end D5.S1.Digit.Infinite.SevenCycleCollisionFuture

namespace D5.S1.Digit.Infinite.SevenCycleActualRecords

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase)
open D5.S1.Digit.Infinite.SevenCycleCollisionData (golden_data budget_bounds)
open D5.S1.Digit.Infinite.SevenCycleCollisionRecords (actual_phase_mod)
open D5.S1.Digit.Infinite.SevenCycleCollisionColors (entry_bounds uniform_colors)

/-- A record uses one error sequence and a uniform strict margin for every observation. -/
private def strictRecord (Q : ℝ → Fin 6) (b : ℝ) (x : LegalDigits) (r : ℕ → Fin 6)
    (e : ℕ → ℝ) (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ ∀ j,
    |e j| ≤ b - epsilon ∧
    kappa (bitShift x (3 * j)) + e j ∈ stateInterval false ∧
    Q (kappa (bitShift x (3 * j)) + e j) = r j

private theorem cell_geometry (c : Fin 6) :
    -1 ≤ cellLower c ∧ cellLower c < cellUpper c ∧ cellUpper c ≤ 1 + t := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  fin_cases c <;> norm_num [cellLower, cellUpper, cuts, lambda] <;>
    (repeat' apply And.intro) <;> linarith only [ht2, hg, hglo, hghi]

private theorem interior_target (a b x r : ℝ) (hab : a < b) (hr : 0 < r)
    (hx : x ∈ Set.Ioo (a - r) (b + r)) :
    ∃ p : ℝ, p ∈ Set.Ioo a b ∧ |p - x| < r := by
  have h : max a (x - r) < min b (x + r) := by
    apply max_lt
    · apply lt_min hab
      linarith [hx.1]
    · apply lt_min
      · linarith [hx.2]
      · linarith
  obtain ⟨p, hp, hp'⟩ := exists_between h
  refine ⟨p, ⟨lt_of_le_of_lt (le_max_left _ _) hp,
    lt_of_lt_of_le hp' (min_le_left _ _)⟩, ?_⟩
  rw [abs_lt]
  have h1 := lt_of_le_of_lt (le_max_right _ _) hp
  have h2 := lt_of_lt_of_le hp' (min_le_right _ _)
  constructor <;> linarith

private theorem periodic_targets : ∃ p : Bool → Fin 7 → ℝ,
    (∀ b j, p b j ∈ Set.Ioo (cellLower (phaseColor j)) (cellUpper (phaseColor j))) ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ b j,
      |p b j - phase (if b then firstEntry else rivalEntry) j| ≤ budget - epsilon := by
  classical
  have hbeta : 0 < budget := budget_bounds.2.2.1
  have h (b : Bool) (j : Fin 7) :
      ∃ p : ℝ, p ∈ Set.Ioo (cellLower (phaseColor j)) (cellUpper (phaseColor j)) ∧
        |p - phase (if b then firstEntry else rivalEntry) j| < budget := by
    apply interior_target _ _ _ _ (cell_geometry _).2.1 hbeta
    by_cases hj : j = 0
    · subst j
      cases b
      · simpa [phase, phaseColor] using entry_bounds.2.2.2.1
      · simpa [phase, phaseColor] using entry_bounds.2.2.1
    · apply uniform_colors _ _ j hj
      cases b
      · exact entry_bounds.2.1
      · exact entry_bounds.1
  choose p hp he using h
  let d (i : Bool × Fin 7) : ℝ :=
    budget - |p i.1 i.2 - phase (if i.1 then firstEntry else rivalEntry) i.2|
  let epsilon := Finset.univ.inf' (Finset.univ_nonempty :
    (Finset.univ : Finset (Bool × Fin 7)).Nonempty) d
  have heps : 0 < epsilon := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    dsimp [d]
    linarith [he i.1 i.2]
  refine ⟨p, hp, epsilon, heps, ?_⟩
  intro b j
  have hd : epsilon ≤ d (b, j) :=
    Finset.inf'_le _ (Finset.mem_univ (b, j))
  dsimp [d] at hd
  linarith

private theorem interior_owned (Q : ℝ → Fin 6) (hQ : instrument Q)
    (c : Fin 6) (p : ℝ) (hp : p ∈ Set.Ioo (cellLower c) (cellUpper c)) :
    Q p = c := by
  obtain ⟨ht2, hg, hg2, hglo, hghi⟩ := golden_data
  have hs : p ∈ stateInterval false := by
    have hc := cell_geometry c
    exact ⟨hc.1.trans hp.1.le, hp.2.le.trans hc.2.2⟩
  have h := hQ p hs
  generalize hd : Q p = d at h ⊢
  fin_cases c <;> fin_cases d <;>
    norm_num [cellLower, cellUpper, cuts, lambda] at hp h ⊢ <;>
      linarith only [hp.1, hp.2, h.1, h.2, ht2, hg, hglo, hghi]

private theorem periodic_actual_records (Q : ℝ → Fin 6) (hQ : instrument Q) :
    ∃ e : Bool → ℕ → ℝ, ∃ epsilon : ℝ,
      strictRecord Q budget (source true)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e true) epsilon ∧
      strictRecord Q budget (source false)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e false) epsilon := by
  obtain ⟨p, hp, epsilon, heps, he⟩ := periodic_targets
  let e (b : Bool) (j : ℕ) := p b ⟨j % 7, Nat.mod_lt _ (by decide)⟩ -
    kappa (bitShift (source b) (3 * j))
  have hr (b : Bool) : strictRecord Q budget (source b)
      (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e b) epsilon := by
    refine ⟨heps, ?_⟩
    intro j
    have hm := actual_phase_mod b j
    have hb : |e b j| ≤ budget - epsilon := by
      dsimp [e]
      rw [hm]
      exact he b _
    have hx : kappa (bitShift (source b) (3 * j)) + e b j =
        p b ⟨j % 7, Nat.mod_lt _ (by decide)⟩ := by dsimp [e]; ring
    rw [hx]
    refine ⟨hb, ?_, interior_owned Q hQ _ _ (hp b _)⟩
    have hc := cell_geometry (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
    exact ⟨hc.1.trans (hp b _).1.le, (hp b _).2.le.trans hc.2.2⟩
  exact ⟨e, epsilon, hr true, hr false⟩

end D5.S1.Digit.Infinite.SevenCycleActualRecords

namespace D5.S1.Digit.Infinite.SevenCycleJointRecords

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase)
open D5.S1.Digit.Infinite.SevenCycleActualRecords (strictRecord)
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open D5.S1.Digit.Infinite.SevenCycleActualRecords (periodic_actual_records interior_owned cell_geometry)
open D5.S1.Digit.Infinite.SevenCycleCollisionData (budget_bounds shifted_source_tail actual_entry)
open D5.S1.Digit.Infinite.SevenCycleCollisionRecords (actual_phase actual_phase_guard)
open D5.S1.Digit.Infinite.SevenCycleCollisionFuture (feeding_scalar)
open D5.S1.Digit.Infinite.SevenCycleCollisionColors (entry_bounds)

private theorem shared_tail_shift (f : LegalDigits)
    (ht : originalT f = originalT (source true)) (j : ℕ) (hj : 0 < j) :
    bitShift f (3 * j) = bitShift (source true) (3 * j) := by
  apply Subtype.ext
  funext i
  have h := congrArg (fun z : LegalDigits => z.val (i + 3 * j - 3)) ht
  simpa only [originalT, bitShift, show i + 3 * j - 3 + 3 = i + 3 * j by omega] using h

private theorem joint_actual_records (Q : ℝ → Fin 6) (hQ : instrument Q) :
    ∃ f : LegalDigits, ∃ e : Bool → ℕ → ℝ, ∃ ef er : ℕ → ℝ, ∃ epsilon : ℝ,
      stateAddress false f ∧ window f 0 = nullLabel ∧
      originalT f = originalT (source true) ∧ kappa f = feedingEntry ∧
      strictRecord Q budget (source true)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e true) epsilon ∧
      strictRecord Q budget (source false)
        (fun j => phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) (e false) epsilon ∧
      strictRecord Q budget f
        (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
        ef epsilon ∧
      strictRecord Q budget (source false)
        (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
        er epsilon ∧
      ef 0 = 0 ∧ er 0 = 0 ∧
      (∀ j, 0 < j → ef j = e true j ∧ er j = e false j) ∧
      e false 0 ≠ 0 ∧ (∀ b, ¬ finiteTail (source b)) ∧ ¬ finiteTail f := by
  have hguard : stateAddress false (originalT (source true)) := by
    change stateAddress false (bitShift (source true) 3)
    convert actual_phase_guard true 1 using 1 <;> norm_num [phaseGuard]
  obtain ⟨f, hf, _⟩ := closed_observation_graph_realization.2.2.2.1 false nullLabel false
    (originalT (source true)) (by simp [lawful, outgoing, nullLabel]) hguard
  have hscalar : kappa f = feedingEntry := by
    rw [(closed_observation_graph_realization.2.2.1 f).1, hf.2.1, hf.2.2]
    change branch nullLabel (kappa (bitShift (source true) (3 * (1 : Fin 7).val))) = _
    rw [actual_phase true 1]
    simpa only [↓reduceIte] using feeding_scalar
  have htail (j : ℕ) (hj : 0 < j) :
      bitShift f (3 * j) = bitShift (source true) (3 * j) := by
    exact shared_tail_shift f hf.2.2 j hj
  obtain ⟨e, epsilon, hu, hv⟩ := periodic_actual_records Q hQ
  let epsilon' := min epsilon budget
  have hp : 0 < epsilon' := lt_min hu.1 budget_bounds.2.2.1
  have hsmall : epsilon' ≤ epsilon := min_le_left _ _
  have hbeta : epsilon' ≤ budget := min_le_right _ _
  have weaken (x : LegalDigits) (r : ℕ → Fin 6) (ex : ℕ → ℝ)
      (hx : strictRecord Q budget x r ex epsilon) : strictRecord Q budget x r ex epsilon' := by
    refine ⟨hp, ?_⟩
    intro j
    obtain ⟨hb, hs, hc⟩ := hx.2 j
    exact ⟨by linarith, hs, hc⟩
  let ef (j : ℕ) := if j = 0 then 0 else e true j
  let er (j : ℕ) := if j = 0 then 0 else e false j
  have make_second (x : LegalDigits) (ex : ℕ → ℝ)
      (h0 : kappa x ∈ Set.Ioo (cellLower 2) (cellUpper 2))
      (hfuture : ∀ j, 0 < j →
        |ex j| ≤ budget - epsilon ∧
        kappa (bitShift x (3 * j)) + ex j ∈ stateInterval false ∧
        Q (kappa (bitShift x (3 * j)) + ex j) =
          phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) :
      strictRecord Q budget x
        (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
        (fun j => if j = 0 then 0 else ex j) epsilon' := by
    refine ⟨hp, ?_⟩
    intro j
    by_cases hj : j = 0
    · subst j
      simp only [↓reduceIte, bitShift, Nat.mul_zero, Nat.add_zero, add_zero, abs_zero]
      refine ⟨by linarith, ?_, interior_owned Q hQ 2 _ h0⟩
      have hc := cell_geometry 2
      exact ⟨hc.1.trans h0.1.le, h0.2.le.trans hc.2.2⟩
    · simp only [hj, ↓reduceIte]
      obtain ⟨hb, hs, hc⟩ := hfuture j (by omega)
      exact ⟨by linarith, hs, hc⟩
  have hfr : strictRecord Q budget f
      (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
      ef epsilon' := by
    refine make_second f (e true) ?_ ?_
    · rw [hscalar]
      exact entry_bounds.2.2.2.2.2
    · intro j hj
      rw [htail j hj]
      exact hu.2 j
  have hvr : strictRecord Q budget (source false)
      (fun j => if j = 0 then 2 else phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩)
      er epsilon' := by
    refine make_second (source false) (e false) ?_ ?_
    · rw [actual_entry]
      exact entry_bounds.2.2.2.2.1
    · exact fun j _ => hv.2 j
  have hn (b : Bool) : ¬ finiteTail (source b) := by
    rintro ⟨N, hN⟩
    have h := hN (21 * (N + 1) + 4) (by omega)
    norm_num [source, Nat.add_mod, Nat.mul_mod] at h
  refine ⟨f, e, ef, er, epsilon', hf.1, hf.2.1, hf.2.2, hscalar,
    weaken _ _ _ hu, weaken _ _ _ hv, hfr, hvr, rfl, rfl, ?_, ?_, hn, ?_⟩
  · intro j hj
    simp [ef, er, show j ≠ 0 by omega]
  · intro he
    have h := (hv.2 0).2.2
    have h2 : Q (kappa (source false)) = 2 := by
      apply interior_owned Q hQ 2
      rw [actual_entry]
      exact entry_bounds.2.2.2.2.1
    simp only [Nat.mul_zero, bitShift, Nat.add_zero, he, add_zero] at h
    rw [h2] at h
    norm_num [phaseColor] at h
    have hc := congrArg Fin.val h
    norm_num at hc
  · rintro ⟨N, hN⟩
    apply hn true
    refine ⟨N + 3, ?_⟩
    intro i hi
    have h := congrArg (fun z : LegalDigits => z.val (i - 3)) hf.2.2
    simp only [originalT, bitShift, Nat.sub_add_cancel (by omega : 3 ≤ i)] at h
    exact h.symm.trans (hN i (by omega))

end D5.S1.Digit.Infinite.SevenCycleJointRecords

namespace D5.S1.Digit.Infinite.SevenCycleActualCollision

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCollisionData (source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry
  referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase)
open D5.S1.Digit.Infinite.SevenCycleActualRecords (strictRecord)
open D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
open D5.S1.Digit.Infinite.SevenCycleJointRecords (joint_actual_records shared_tail_shift)
open D5.S1.Digit.Infinite.SevenCycleCollisionData (budget_bounds shifted_source_tail shifted_source_windows actual_entry entry_fixed)
open D5.S1.Digit.Infinite.SevenCycleCollisionRecords (actual_phase_mod phase_state)
open D5.S1.Digit.Infinite.SevenCycleCollisionFuture (phase_lawful)

private theorem strict_member (Q : ℝ → Fin 6) (hQ : instrument Q) (x : LegalDigits)
    (r : ℕ → Fin 6) (e : ℕ → ℝ) (epsilon : ℝ)
    (hx : strictRecord Q budget x r e epsilon) (j : ℕ) :
    kappa (bitShift x (3 * j)) ∈ observation budget (r j) := by
  apply (D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width.2.2.2.2.2.2.2.2.2.1 Q hQ
    budget budget_bounds.2.2.1.le (r j))
  refine ⟨?_, kappa (bitShift x (3 * j)) + e j, (hx.2 j).2.1, (hx.2 j).2.2, ?_⟩
  · rw [← closed_observation_graph_realization.2.1 false]
    exact ⟨_, by simp [stateAddress], rfl⟩
  · have h := (hx.2 j).1
    have he : |kappa (bitShift x (3 * j)) -
        (kappa (bitShift x (3 * j)) + e j)| = |e j| := by
      rw [show kappa (bitShift x (3 * j)) -
        (kappa (bitShift x (3 * j)) + e j) = -e j by ring, abs_neg]
    rw [he]
    linarith [hx.1]

private theorem actual_collision :
    kappa (source false) ∈ observation budget 1 ∧
    kappa (source false) ∈ observation budget 2 ∧
    ∀ n : ℕ, phase firstEntry 1 ∈ entrySet budget threeLabel nullLabel 1 2 false ∩
      horizon budget (source false) 1 false n := by
  obtain ⟨Q, hQ, _, _⟩ := D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨f, e, ef, er, epsilon, hf, hl, ht, hz, hu, hv, hfr, hvr, _, _, _⟩ :=
    joint_actual_records Q hQ
  have htail (j : ℕ) (hj : 0 < j) :
      bitShift f (3 * j) = bitShift (source true) (3 * j) := by
    exact shared_tail_shift f ht j hj
  have hfirst : kappa (source true) ∈ observation budget 1 := by
    simpa [phaseColor, bitShift] using strict_member Q hQ _ _ _ _ hu 0
  have hrival1 : kappa (source false) ∈ observation budget 1 := by
    simpa [phaseColor, bitShift] using strict_member Q hQ _ _ _ _ hv 0
  have hrival2 : kappa (source false) ∈ observation budget 2 := by
    simpa [bitShift] using strict_member Q hQ _ _ _ _ hvr 0
  have hfeeding : feedingEntry ∈ observation budget 2 := by
    have h := strict_member Q hQ _ _ _ _ hfr 0
    simpa [bitShift, hz] using h
  refine ⟨hrival1, hrival2, ?_⟩
  intro n
  have all_future (n j : ℕ) (hj : 0 < j) :
      kappa (bitShift (source true) (3 * j)) ∈
        horizon budget (source false) j
          (phaseGuard ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n := by
    induction n generalizing j with
    | zero =>
      change _ ∈ stateInterval _
      rw [actual_phase_mod]
      exact phase_state true j
    | succ n ih =>
      have hx := strict_member Q hQ _ _ _ _ hfr j
      have hy := strict_member Q hQ _ _ _ _ hvr j
      simp only [show j ≠ 0 by omega, ↓reduceIte] at hx hy
      rw [htail j hj] at hx
      refine ⟨⟨phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩, hy, hx⟩,
        window (source true) j, phaseGuard ⟨(j + 1) % 7, Nat.mod_lt _ (by decide)⟩,
        phase_lawful true j, kappa (bitShift (source true) (3 * (j + 1))),
        ih (j + 1) (by omega), ?_⟩
      have h := (closed_observation_graph_realization.2.2.1
        (bitShift (source true) (3 * j))).1
      simpa only [shifted_source_windows, Nat.add_zero, shifted_source_tail] using h
  have hs : phase firstEntry 1 ∈ stateInterval false := by
    convert phase_state true 1 using 1 <;> norm_num [phaseGuard]
  have h1 : branch threeLabel (phase firstEntry 1) ∈ observation budget 1 := by
    rw [actual_entry] at hfirst
    have he := entry_fixed true
    simp only [↓reduceIte] at he hfirst
    rwa [← he]
  have h2 : branch nullLabel (phase firstEntry 1) ∈ observation budget 2 := by
    have h := (closed_observation_graph_realization.2.2.1 f).1
    rw [hl, ht] at h
    change kappa f = branch nullLabel (kappa (bitShift (source true) (3 * 1))) at h
    rw [actual_phase_mod] at h
    norm_num at h
    rw [← h]
    simpa [bitShift, hz] using hfeeding
  refine ⟨⟨⟨hs, h1⟩, h2⟩, ?_⟩
  have h := all_future n 1 (by decide)
  rw [actual_phase_mod] at h
  convert h using 1 <;> norm_num [phaseGuard]

end D5.S1.Digit.Infinite.SevenCycleActualCollision
