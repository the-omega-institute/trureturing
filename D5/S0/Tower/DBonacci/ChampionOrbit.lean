/- GID: D5/S0/Tower/DBonacci/ChampionOrbit
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/ChampionOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A closed four-bonacci period-two point refutes the initial champion formula. -/

import D5.S0.Tower.DBonacci.Substitution
import D5.S0.Tower.DBonacci.Survivor

namespace D5.S0.Tower.DBonacci.ChampionOrbit

open D5.S0.Tower.DBonacci.Gaps
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.DBonacci.Survivor
open D5.S0.Tower.DBonacci.Values

local notation "b" => dbonacciPerronRoot 4
local notation "largeLeft" => b / (b ^ 2 - 1)
local notation "lowArm" => (b ^ 2 - b - 1) / (b ^ 2 - 1)
local notation "middleLeft" => 1 / (b ^ 2 - 1)
local notation "middleRight" => b * lowArm

/- Library-search audit trail (2026-08-17):
   * Repository search found the general local d-bonacci substitution and the
     frozen Tribonacci period-two proof shape, but no order-four orbit theorem.
   * Pinned mathlib supplies the ordered-grid infimum-distance and filter
     liminf lemmas used below; it has no four-bonacci champion result.
   * Loogle returned only generic `Filter.liminf` and `Function.Periodic`
     suggestions. LeanSearch's public API endpoint returned HTTP 404. -/

/-- The point with tail digits `1010...` beginning at position five. -/
noncomputable def dbonacciFourChampionPoint : Real :=
  b ^ (-3 : Int) / (b ^ 2 - 1)

/-- A labeled adjacent gap records both normalized endpoint arms. -/
def IsDBonacciOrbitGap (d Q : Nat) (x : Real) (label : Nat)
    (leftArm rightArm : Real) : Prop :=
  ∃ i : Fin (dbonacci d (Q + 2) - 1),
    indexedNameValue d Q (gapRight d Q i) -
          indexedNameValue d Q (gapLeft d Q i) =
        dbonacciGapLength d Q label ∧
      x - indexedNameValue d Q (gapLeft d Q i) =
        leftArm * (dbonacciPerronRoot d) ^ (-(Q : Int)) ∧
      indexedNameValue d Q (gapRight d Q i) - x =
        rightArm * (dbonacciPerronRoot d) ^ (-(Q : Int))

theorem four_root_bounds : 1 < b ∧ b < 2 := by
  exact ⟨one_lt_dbonacciPerronRoot 4 (by norm_num),
    dbonacciPerronRoot_lt_two 4 (by norm_num)⟩

theorem four_root_characteristic : b ^ 4 = b ^ 3 + b ^ 2 + b + 1 := by
  have h := dbonacciPerronRoot_characteristic 4 (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  nlinarith

theorem four_denominator_pos : 0 < b ^ 2 - 1 := by
  nlinarith [four_root_bounds.1]

theorem four_lowArm_pos : 0 < lowArm := by
  have hbphi : Real.goldenRatio < b := by
    rw [← dbonacciPerronRoot_two_eq_goldenRatio]
    exact dbonacciPerronRoot_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  have hphi := Real.goldenRatio_sq
  have hproduct :
      0 < (b - Real.goldenRatio) * (b + Real.goldenRatio - 1) := by
    exact mul_pos (sub_pos.mpr hbphi) (by nlinarith [Real.one_lt_goldenRatio])
  have hnum : 0 < b ^ 2 - b - 1 := by
    nlinarith
  exact div_pos hnum four_denominator_pos

theorem four_middleLeft_pos : 0 < middleLeft :=
  one_div_pos.mpr four_denominator_pos

theorem four_lowArm_lt_middleLeft : lowArm < middleLeft := by
  rw [div_lt_div_iff_of_pos_right four_denominator_pos]
  nlinarith [four_root_bounds.2, four_root_bounds.1]

theorem four_middleLeft_le_middleRight : middleLeft ≤ middleRight := by
  have hproduct : b * (b ^ 3 - b ^ 2 - b - 1) = 1 := by
    nlinarith [four_root_characteristic]
  have hpositive : 0 < b ^ 3 - b ^ 2 - b - 1 := by
    nlinarith [four_root_bounds.1]
  have hdifference :
      middleRight - middleLeft =
        (b ^ 3 - b ^ 2 - b - 1) / (b ^ 2 - 1) := by
    field_simp [four_denominator_pos.ne']
  rw [← sub_nonneg, hdifference]
  exact div_nonneg hpositive.le four_denominator_pos.le

theorem four_lowArm_lt_largeLeft : lowArm < largeLeft := by
  exact four_lowArm_lt_middleLeft.trans (by
    apply div_lt_div_of_pos_right
    · exact four_root_bounds.1
    · exact four_denominator_pos)

theorem four_coordinate_sum : largeLeft + lowArm = 1 := by
  field_simp [four_denominator_pos.ne']
  ring

theorem four_large_branch : b * largeLeft - 1 = middleLeft := by
  field_simp [four_denominator_pos.ne']
  ring

theorem four_middle_branch : b * middleLeft = largeLeft := by
  field_simp [four_denominator_pos.ne']

theorem four_middle_complement : 1 - b * middleLeft = lowArm := by
  rw [four_middle_branch]
  nlinarith [four_coordinate_sum]

theorem four_scale_succ (Q : Nat) :
    b ^ (-(Q : Int)) = b * b ^ (-((Q + 1 : Nat) : Int)) := by
  calc
    b ^ (-(Q : Int)) = b ^ ((1 : Int) + -((Q + 1 : Nat) : Int)) := by
      congr 1
      push_cast
      omega
    _ = b ^ (1 : Int) * b ^ (-((Q + 1 : Nat) : Int)) := by
      rw [zpow_add₀ (ne_of_gt (zero_lt_one.trans four_root_bounds.1))]
    _ = b * b ^ (-((Q + 1 : Nat) : Int)) := by rw [zpow_one]

theorem four_top_gap_length (Q : Nat) :
    dbonacciGapLength 4 Q 3 = b ^ (-(Q : Int)) := by
  unfold dbonacciGapLength
  have hfull : dbonacciBudgetBound 4 3 = 1 := by
    simpa using dbonacciBudgetBound_full 4 (by norm_num)
  rw [hfull, mul_one, zpow_neg, zpow_natCast, inv_pow]

/-- A positive labeled coarse gap has exactly one inserted name and two stated children. -/
theorem positive_gap_substitution (d Q fuel : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1))
    (hgap : indexedNameValue d Q (gapRight d Q i) -
        indexedNameValue d Q (gapLeft d Q i) =
      dbonacciGapLength d Q (fuel + 1)) :
    ∃ j : Fin (dbonacci d (Q + 3)),
      insertedNameIndices d Q i = {j} ∧
        indexedNameValue d (Q + 1) j -
            indexedNameValue d Q (gapLeft d Q i) =
          dbonacciGapLength d (Q + 1) (d - 1) ∧
        indexedNameValue d Q (gapRight d Q i) -
            indexedNameValue d (Q + 1) j =
          dbonacciGapLength d (Q + 1) fuel := by
  obtain ⟨j, hset⟩ := Finset.card_eq_one.mp
    (succ_gap_insertion_count d Q fuel hd i hgap)
  have hj : j ∈ insertedNameIndices d Q i := by
    rw [hset]
    simp
  have hvalue := insertedNameValue_eq d Q hd i j hj
  have htop := newDigitWeight_eq_topGap d Q hd
  have hsplit := gapLength_succ_substitution d Q fuel hd
  refine ⟨j, hset, ?_, ?_⟩ <;> linarith

theorem inserted_singleton_positions (d Q : Nat)
    (i : Fin (dbonacci d (Q + 2) - 1))
    (j : Fin (dbonacci d (Q + 3)))
    (hset : insertedNameIndices d Q i = {j}) :
    (levelEmbedding d Q (gapLeft d Q i)).1 + 1 = j.1 ∧
      j.1 + 1 = (levelEmbedding d Q (gapRight d Q i)).1 := by
  have hj : j ∈ insertedNameIndices d Q i := by
    rw [hset]
    simp
  have hjbounds :
      levelEmbedding d Q (gapLeft d Q i) < j ∧
        j < levelEmbedding d Q (gapRight d Q i) := by
    simpa only [insertedNameIndices, Finset.mem_Ioo] using hj
  have hcard : (insertedNameIndices d Q i).card = 1 := by
    rw [hset]
    simp
  rw [insertedNameIndices, Fin.card_Ioo] at hcard
  constructor <;> omega

theorem dbonacci_four_six_eq : dbonacci 4 6 = 15 := by
  rw [show 6 = 4 + 2 by omega, dbonacci_add_two_of_le 4 4 (by omega),
    Finset.sum_fin_eq_sum_range]
  norm_num [Finset.sum_range_succ, dbonacci_add_two_of_lt]

theorem four_short_bounded_card (Q : Nat) (hQ : Q < 4) :
    Fintype.card (BoundedRunName 3 3 Q) = 2 ^ Q := by
  rw [← dbonacci_name_card_eq_bounded 3 Q, dbonacci_name_card_of_lt 4 Q hQ]

/-- The large labeled phase takes the right branch into a label-two gap. -/
theorem four_large_to_middle (Q : Nat)
    (hgap : IsDBonacciOrbitGap 4 Q dbonacciFourChampionPoint 3
      largeLeft lowArm) :
    IsDBonacciOrbitGap 4 (Q + 1) dbonacciFourChampionPoint 2
      middleLeft middleRight := by
  rcases hgap with ⟨i, hlength, hleft, hright⟩
  obtain ⟨j, hset, hjleft, hjright⟩ :=
    positive_gap_substitution 4 Q 2 (by norm_num) i (by simpa using hlength)
  have hpositions := inserted_singleton_positions 4 Q i j hset
  let next : Fin (dbonacci 4 ((Q + 1) + 2) - 1) :=
    ⟨j.1, by
      change j.1 < dbonacci 4 (Q + 3) - 1
      have hrightbound := (levelEmbedding 4 Q (gapRight 4 Q i)).2
      omega⟩
  have hnextLeft : gapLeft 4 (Q + 1) next = j := by
    apply Fin.ext
    rfl
  have hnextRight :
      gapRight 4 (Q + 1) next = levelEmbedding 4 Q (gapRight 4 Q i) := by
    apply Fin.ext
    exact hpositions.2
  refine ⟨next, ?_, ?_, ?_⟩
  · rw [hnextLeft, hnextRight, levelEmbedding_value]
    exact hjright
  · rw [hnextLeft]
    calc
      dbonacciFourChampionPoint - indexedNameValue 4 (Q + 1) j =
          (dbonacciFourChampionPoint - indexedNameValue 4 Q (gapLeft 4 Q i)) -
            (indexedNameValue 4 (Q + 1) j -
              indexedNameValue 4 Q (gapLeft 4 Q i)) := by ring
      _ = largeLeft * b ^ (-(Q : Int)) -
          b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [hleft, hjleft, four_top_gap_length]
      _ = (b * largeLeft - 1) * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [four_scale_succ Q]
            ring
      _ = middleLeft * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [four_large_branch]
  · rw [hnextRight, levelEmbedding_value]
    calc
      indexedNameValue 4 Q (gapRight 4 Q i) - dbonacciFourChampionPoint =
          lowArm * b ^ (-(Q : Int)) := hright
      _ = middleRight * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [four_scale_succ Q]
            ring

/-- The label-two phase takes the left branch back to the large labeled gap. -/
theorem four_middle_to_large (Q : Nat)
    (hgap : IsDBonacciOrbitGap 4 Q dbonacciFourChampionPoint 2
      middleLeft middleRight) :
    IsDBonacciOrbitGap 4 (Q + 1) dbonacciFourChampionPoint 3
      largeLeft lowArm := by
  rcases hgap with ⟨i, hlength, hleft, hright⟩
  obtain ⟨j, hset, hjleft, _⟩ :=
    positive_gap_substitution 4 Q 1 (by norm_num) i (by simpa using hlength)
  have hpositions := inserted_singleton_positions 4 Q i j hset
  let next : Fin (dbonacci 4 ((Q + 1) + 2) - 1) :=
    ⟨(levelEmbedding 4 Q (gapLeft 4 Q i)).1, by
      change (levelEmbedding 4 Q (gapLeft 4 Q i)).1 < dbonacci 4 (Q + 3) - 1
      have hjbound := j.2
      omega⟩
  have hnextLeft :
      gapLeft 4 (Q + 1) next = levelEmbedding 4 Q (gapLeft 4 Q i) := by
    apply Fin.ext
    rfl
  have hnextRight : gapRight 4 (Q + 1) next = j := by
    apply Fin.ext
    exact hpositions.1
  refine ⟨next, ?_, ?_, ?_⟩
  · rw [hnextLeft, hnextRight, levelEmbedding_value]
    exact hjleft
  · rw [hnextLeft, levelEmbedding_value]
    calc
      dbonacciFourChampionPoint - indexedNameValue 4 Q (gapLeft 4 Q i) =
          middleLeft * b ^ (-(Q : Int)) := hleft
      _ = largeLeft * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [four_scale_succ Q]
            calc
              middleLeft * (b * b ^ (-((Q + 1 : Nat) : Int))) =
                  (b * middleLeft) * b ^ (-((Q + 1 : Nat) : Int)) := by ring
              _ = largeLeft * b ^ (-((Q + 1 : Nat) : Int)) := by
                rw [four_middle_branch]
  · rw [hnextRight]
    calc
      indexedNameValue 4 (Q + 1) j - dbonacciFourChampionPoint =
          (indexedNameValue 4 (Q + 1) j -
              indexedNameValue 4 Q (gapLeft 4 Q i)) -
            (dbonacciFourChampionPoint - indexedNameValue 4 Q (gapLeft 4 Q i)) := by
              ring
      _ = b ^ (-((Q + 1 : Nat) : Int)) -
          middleLeft * b ^ (-(Q : Int)) := by
            rw [hjleft, four_top_gap_length, hleft]
      _ = (1 - b * middleLeft) * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [four_scale_succ Q]
            ring
      _ = lowArm * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [four_middle_complement]

theorem four_first_index_zero :
    indexedNameValue 4 4 ⟨0, by rw [dbonacci_four_six_eq]; omega⟩ = 0 := by
  rw [indexedNameValue_succ_eq_bounded]
  have hindex :
      Fin.cast
          ((dbonacci_name_card 4 4).symm.trans
            (dbonacci_name_card_eq_bounded 3 4))
          ⟨0, by rw [dbonacci_four_six_eq]; omega⟩ =
        ⟨0, bounded_run_level_pos 3 3 4⟩ := by
    apply Fin.ext
    rfl
  rw [hindex, boundedIndexedNameValue_zero]

theorem four_first_index_one :
    indexedNameValue 4 4 ⟨1, by rw [dbonacci_four_six_eq]; omega⟩ =
      b ^ (-4 : Int) := by
  rw [indexedNameValue_succ_eq_bounded]
  let i4 := Fin.cast
    ((dbonacci_name_card 4 4).symm.trans (dbonacci_name_card_eq_bounded 3 4))
      (⟨1, by rw [dbonacci_four_six_eq]; omega⟩ : Fin (dbonacci 4 6))
  have hi4 : i4.1 < Fintype.card (BoundedRunName 3 3 3) := by
    have hcard : 1 < Fintype.card (BoundedRunName 3 3 3) := by
      rw [four_short_bounded_card 3 (by omega)]
      norm_num
    simpa only [i4, Fin.val_cast] using hcard
  rw [show Fin.cast
      ((dbonacci_name_card 4 4).symm.trans (dbonacci_name_card_eq_bounded 3 4))
        (⟨1, by rw [dbonacci_four_six_eq]; omega⟩ : Fin (dbonacci 4 6)) = i4
      by rfl,
    boundedIndexedNameValue_lower 3 2 3 i4 hi4]
  let i3 : Fin (Fintype.card (BoundedRunName 3 3 3)) := ⟨i4.1, hi4⟩
  have hi3 : i3.1 < Fintype.card (BoundedRunName 3 3 2) := by
    have hcard : 1 < Fintype.card (BoundedRunName 3 3 2) := by
      rw [four_short_bounded_card 2 (by omega)]
      norm_num
    simpa only [i3, i4, Fin.val_cast] using hcard
  rw [show (⟨i4.1, hi4⟩ : Fin (Fintype.card (BoundedRunName 3 3 3))) = i3 by rfl,
    boundedIndexedNameValue_lower 3 2 2 i3 hi3]
  let i2 : Fin (Fintype.card (BoundedRunName 3 3 2)) := ⟨i3.1, hi3⟩
  have hi2 : i2.1 < Fintype.card (BoundedRunName 3 3 1) := by
    have hcard : 1 < Fintype.card (BoundedRunName 3 3 1) := by
      rw [four_short_bounded_card 1 (by omega)]
      norm_num
    simpa only [i2, i3, i4, Fin.val_cast] using hcard
  rw [show (⟨i3.1, hi3⟩ : Fin (Fintype.card (BoundedRunName 3 3 2))) = i2 by rfl,
    boundedIndexedNameValue_lower 3 2 1 i2 hi2]
  let i1 : Fin (Fintype.card (BoundedRunName 3 3 1)) := ⟨i2.1, hi2⟩
  have hi1 : Fintype.card (BoundedRunName 3 3 0) ≤ i1.1 := by
    have hcard : Fintype.card (BoundedRunName 3 3 0) ≤ 1 := by
      rw [four_short_bounded_card 0 (by omega)]
      norm_num
    simpa only [i1, i2, i3, i4, Fin.val_cast] using hcard
  rw [show (⟨i2.1, hi2⟩ : Fin (Fintype.card (BoundedRunName 3 3 1))) = i1 by rfl,
    boundedIndexedNameValue_upper 3 2 0 i1 hi1]
  have hi1val : i1.1 = 1 := by
    simp only [i1, i2, i3, i4, Fin.val_cast]
  have hcardFullZero : Fintype.card (BoundedRunName 3 3 0) = 1 := by
    rw [four_short_bounded_card 0 (by omega)]
    norm_num
  have hzero :
      boundedIndexedNameValue 3 2 0
          ⟨i1.1 - Fintype.card (BoundedRunName 3 3 0), by
            rw [hi1val, hcardFullZero]
            exact bounded_run_level_pos 3 2 0⟩ = 0 := by
    have hindex :
        (⟨i1.1 - Fintype.card (BoundedRunName 3 3 0), by
            rw [hi1val, hcardFullZero]
            exact bounded_run_level_pos 3 2 0⟩ :
          Fin (Fintype.card (BoundedRunName 3 2 0))) =
        ⟨0, bounded_run_level_pos 3 2 0⟩ := by
      apply Fin.ext
      change i1.1 - Fintype.card (BoundedRunName 3 3 0) = 0
      omega
    rw [hindex, boundedIndexedNameValue_zero]
  rw [hzero]
  simp only [mul_zero, add_zero]
  change b⁻¹ * (b⁻¹ * (b⁻¹ * b⁻¹)) = b ^ (-4 : Int)
  rw [zpow_neg]
  calc
    b⁻¹ * (b⁻¹ * (b⁻¹ * b⁻¹)) = b⁻¹ ^ 4 := by ring
    _ = (b ^ 4)⁻¹ := inv_pow b 4

theorem four_champion_point_scaled :
    dbonacciFourChampionPoint = largeLeft * b ^ (-4 : Int) := by
  unfold dbonacciFourChampionPoint
  have hscale : b ^ (-3 : Int) = b * b ^ (-4 : Int) := by
    calc
      b ^ (-3 : Int) = b ^ ((1 : Int) + (-4 : Int)) := by norm_num
      _ = b ^ (1 : Int) * b ^ (-4 : Int) := by
        rw [zpow_add₀ (ne_of_gt (zero_lt_one.trans four_root_bounds.1))]
      _ = b * b ^ (-4 : Int) := by rw [zpow_one]
  rw [hscale]
  ring

/-- The closed point starts in the first level-four largest gap. -/
theorem four_champion_base_gap :
    IsDBonacciOrbitGap 4 4 dbonacciFourChampionPoint 3 largeLeft lowArm := by
  let i : Fin (dbonacci 4 (4 + 2) - 1) :=
    ⟨0, by rw [dbonacci_four_six_eq]; omega⟩
  have hleft : gapLeft 4 4 i =
      (⟨0, by rw [dbonacci_four_six_eq]; omega⟩ : Fin (dbonacci 4 6)) := by
    apply Fin.ext
    rfl
  have hright : gapRight 4 4 i =
      (⟨1, by rw [dbonacci_four_six_eq]; omega⟩ : Fin (dbonacci 4 6)) := by
    apply Fin.ext
    rfl
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [hleft, hright, four_first_index_zero, four_first_index_one, sub_zero]
    exact (four_top_gap_length 4).symm
  · rw [hleft, four_first_index_zero, sub_zero]
    exact four_champion_point_scaled
  · rw [hright, four_first_index_one, four_champion_point_scaled]
    calc
      b ^ (-4 : Int) - largeLeft * b ^ (-4 : Int) =
          (1 - largeLeft) * b ^ (-4 : Int) := by ring
      _ = lowArm * b ^ (-4 : Int) := by
            rw [show 1 - largeLeft = lowArm by nlinarith [four_coordinate_sum]]

/-- The containing labeled gap has the exact right-left period two. -/
theorem four_champion_gap_orbit (k : Nat) :
    IsDBonacciOrbitGap 4 (2 * k + 4) dbonacciFourChampionPoint 3
        largeLeft lowArm ∧
      IsDBonacciOrbitGap 4 (2 * k + 5) dbonacciFourChampionPoint 2
        middleLeft middleRight := by
  induction k with
  | zero =>
      have hlarge := four_champion_base_gap
      refine ⟨?_, ?_⟩
      · simpa using hlarge
      · simpa using four_large_to_middle 4 hlarge
  | succ k ih =>
      have hlarge := four_middle_to_large (2 * k + 5) ih.2
      have hmiddle := four_large_to_middle (2 * k + 6) hlarge
      constructor
      · convert hlarge using 1
        omega
      · convert hmiddle using 1
        omega

theorem dbonacciSurvivor_eq_of_orbit_gap (d Q : Nat) (hd : 2 ≤ d)
    (x : Real) (label : Nat) (leftArm rightArm arm : Real)
    (hgap : IsDBonacciOrbitGap d Q x label leftArm rightArm)
    (hleftArm : 0 ≤ leftArm) (hrightArm : 0 ≤ rightArm)
    (harmLeft : arm ≤ leftArm) (harmRight : arm ≤ rightArm)
    (hnearest : arm = leftArm ∨ arm = rightArm) :
    dbonacciSurvivor d Q x = arm := by
  rcases hgap with ⟨i, _, hleft, hright⟩
  let left := indexedNameValue d Q (gapLeft d Q i)
  let right := indexedNameValue d Q (gapRight d Q i)
  have hscale_nonneg : 0 ≤ (dbonacciPerronRoot d) ^ (-(Q : Int)) :=
    (zpow_pos (zero_lt_one.trans (one_lt_dbonacciPerronRoot d hd)) _).le
  have hleft_nonneg : 0 ≤ x - left := by
    rw [show x - left = leftArm * (dbonacciPerronRoot d) ^ (-(Q : Int)) by
      exact hleft]
    positivity
  have hright_nonneg : 0 ≤ right - x := by
    rw [show right - x = rightArm * (dbonacciPerronRoot d) ^ (-(Q : Int)) by
      exact hright]
    positivity
  have hgrid : (dbonacciNameGrid d Q).Nonempty := by
    rw [dbonacciNameGrid_eq_indexedNameValue_range]
    exact ⟨left, gapLeft d Q i, rfl⟩
  have hlower : arm * (dbonacciPerronRoot d) ^ (-(Q : Int)) ≤
      Metric.infDist x (dbonacciNameGrid d Q) := by
    rw [Metric.le_infDist hgrid]
    intro y hy
    rw [dbonacciNameGrid_eq_indexedNameValue_range] at hy
    rcases hy with ⟨j, rfl⟩
    by_cases hjleft : j ≤ gapLeft d Q i
    · have hy_le : indexedNameValue d Q j ≤ left :=
        (indexed_nameValue_strictMono d Q hd).monotone hjleft
      have hy_x : indexedNameValue d Q j ≤ x := hy_le.trans (sub_nonneg.mp hleft_nonneg)
      have hscaled := mul_le_mul_of_nonneg_right harmLeft hscale_nonneg
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy_x)]
      linarith
    · have hright_le : gapRight d Q i ≤ j := by
        change i.1 + 1 ≤ j.1
        change ¬j.1 ≤ i.1 at hjleft
        omega
      have hb_le : right ≤ indexedNameValue d Q j :=
        (indexed_nameValue_strictMono d Q hd).monotone hright_le
      have hx_y : x ≤ indexedNameValue d Q j :=
        (sub_nonneg.mp hright_nonneg).trans hb_le
      have hscaled := mul_le_mul_of_nonneg_right harmRight hscale_nonneg
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx_y)]
      linarith
  have hupper : Metric.infDist x (dbonacciNameGrid d Q) ≤
      arm * (dbonacciPerronRoot d) ^ (-(Q : Int)) := by
    rcases hnearest with hnear | hnear
    · calc
        Metric.infDist x (dbonacciNameGrid d Q) ≤ dist x left := by
          apply Metric.infDist_le_dist_of_mem
          rw [dbonacciNameGrid_eq_indexedNameValue_range]
          exact ⟨gapLeft d Q i, rfl⟩
        _ = x - left := by rw [Real.dist_eq, abs_of_nonneg hleft_nonneg]
        _ = arm * (dbonacciPerronRoot d) ^ (-(Q : Int)) := by rw [hleft, hnear]
    · calc
        Metric.infDist x (dbonacciNameGrid d Q) ≤ dist x right := by
          apply Metric.infDist_le_dist_of_mem
          rw [dbonacciNameGrid_eq_indexedNameValue_range]
          exact ⟨gapRight d Q i, rfl⟩
        _ = right - x := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (sub_nonneg.mp hright_nonneg))]
          ring
        _ = arm * (dbonacciPerronRoot d) ^ (-(Q : Int)) := by rw [hright, hnear]
  have hinf : Metric.infDist x (dbonacciNameGrid d Q) =
      arm * (dbonacciPerronRoot d) ^ (-(Q : Int)) := le_antisymm hupper hlower
  have hcancel : (dbonacciPerronRoot d) ^ (Q : Int) *
      (dbonacciPerronRoot d) ^ (-(Q : Int)) = 1 := by
    rw [← zpow_add₀ (ne_of_gt (zero_lt_one.trans (one_lt_dbonacciPerronRoot d hd)))]
    simp
  unfold dbonacciSurvivor
  rw [hinf]
  calc
    (dbonacciPerronRoot d) ^ (Q : Int) *
          (arm * (dbonacciPerronRoot d) ^ (-(Q : Int))) =
        arm * ((dbonacciPerronRoot d) ^ (Q : Int) *
          (dbonacciPerronRoot d) ^ (-(Q : Int))) := by ring
    _ = arm := by rw [hcancel]; ring

theorem four_champion_survivor_even (k : Nat) :
    dbonacciSurvivor 4 (2 * k + 4) dbonacciFourChampionPoint = lowArm := by
  apply dbonacciSurvivor_eq_of_orbit_gap 4 (2 * k + 4) (by norm_num)
      (hgap := (four_champion_gap_orbit k).1)
  · exact (div_pos (zero_lt_one.trans four_root_bounds.1) four_denominator_pos).le
  · exact four_lowArm_pos.le
  · exact four_lowArm_lt_largeLeft.le
  · exact le_rfl
  · exact Or.inr rfl

theorem four_champion_survivor_odd (k : Nat) :
    dbonacciSurvivor 4 (2 * k + 5) dbonacciFourChampionPoint = middleLeft := by
  apply dbonacciSurvivor_eq_of_orbit_gap 4 (2 * k + 5) (by norm_num)
      (hgap := (four_champion_gap_orbit k).2)
  · exact four_middleLeft_pos.le
  · exact mul_nonneg (zero_le_one.trans four_root_bounds.1.le) four_lowArm_pos.le
  · exact le_rfl
  · exact four_middleLeft_le_middleRight
  · exact Or.inl rfl

/-- The four-bonacci period-two point has the corrected closed liminf arm. -/
theorem dbonacci_four_champion_liminf :
    Filter.liminf (fun Q => dbonacciSurvivor 4 Q dbonacciFourChampionPoint)
        Filter.atTop = lowArm := by
  have heventually_lower :
      ∀ᶠ Q in Filter.atTop,
        lowArm ≤ dbonacciSurvivor 4 Q dbonacciFourChampionPoint := by
    rw [Filter.eventually_atTop]
    refine ⟨4, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 4 := ⟨Q - 4, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [four_champion_survivor_even]
    · subst n
      rw [show (2 * k + 1) + 4 = 2 * k + 5 by omega,
        four_champion_survivor_odd]
      exact four_lowArm_lt_middleLeft.le
  have heventually_upper :
      ∀ᶠ Q in Filter.atTop,
        dbonacciSurvivor 4 Q dbonacciFourChampionPoint ≤ middleLeft := by
    rw [Filter.eventually_atTop]
    refine ⟨4, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 4 := ⟨Q - 4, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [four_champion_survivor_even]
      exact four_lowArm_lt_middleLeft.le
    · subst n
      rw [show (2 * k + 1) + 4 = 2 * k + 5 by omega,
        four_champion_survivor_odd]
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨2 * N + 4, by omega, ?_⟩
      rw [four_champion_survivor_even]
    · exact ⟨lowArm, heventually_lower⟩
  · exact Filter.le_liminf_of_le
      (Filter.IsBoundedUnder.isCoboundedUnder_ge ⟨middleLeft, heventually_upper⟩)
      heventually_lower

/-- The initial `(1-beta^-1)/2` candidate is strictly below the actual d=4 liminf. -/
theorem dbonacci_four_initial_candidate_lt_liminf :
    (1 - b⁻¹) / 2 <
      Filter.liminf (fun Q => dbonacciSurvivor 4 Q dbonacciFourChampionPoint)
        Filter.atTop := by
  rw [dbonacci_four_champion_liminf]
  have hbpos : 0 < b := zero_lt_one.trans four_root_bounds.1
  have hfactor : b * (b ^ 3 - b ^ 2 - b - 1) = 1 := by
    nlinarith [four_root_characteristic]
  have hnum : 0 < b ^ 3 - b ^ 2 - b - 1 := by
    nlinarith
  have hcandidate : (1 - b⁻¹) / 2 = (b - 1) / (2 * b) := by
    field_simp [hbpos.ne']
  rw [hcandidate, div_lt_div_iff₀ (mul_pos (by norm_num) hbpos) four_denominator_pos]
  nlinarith

theorem dbonacci_four_initial_candidate_ne_liminf :
    (1 - b⁻¹) / 2 ≠
      Filter.liminf (fun Q => dbonacciSurvivor 4 Q dbonacciFourChampionPoint)
        Filter.atTop :=
  ne_of_lt dbonacci_four_initial_candidate_lt_liminf

end D5.S0.Tower.DBonacci.ChampionOrbit
