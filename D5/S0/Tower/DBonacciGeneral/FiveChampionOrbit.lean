/- GID: D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/FiveChampionOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The five-bonacci period-two orbit has the corrected champion liminf. -/

import D5.S0.Tower.DBonacci.ChampionOrbit
import D5.S0.Tower.DBonacciGeneral.ChampionValue

namespace D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit

open D5.S0.Tower.DBonacci.ChampionOrbit
open D5.S0.Tower.DBonacci.Gaps
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.DBonacci.Survivor
open D5.S0.Tower.DBonacci.Values
open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.Tribonacci.PerronRoot
open D5.S0.Tower.Tribonacci.Values

local notation "b" => dbonacciPerronRoot 5
local notation "largeLeft" => b / (b ^ 2 - 1)
local notation "lowArm" => (b ^ 2 - b - 1) / (b ^ 2 - 1)
local notation "middleLeft" => 1 / (b ^ 2 - 1)
local notation "middleRight" => b * lowArm

/- Library-search audit trail (2026-08-17):
   * Repository search found r73b's general survivor carrier, labeled-gap
     substitution lemmas, and the order-four period-two proof shape.
   * Pinned mathlib supplies the ordered-grid liminf lemmas already packaged
     by r73b; no five-bonacci orbit theorem or third-party dependency exists. -/

/-- The point with tail digits `1010...` beginning at position six. -/
noncomputable def dbonacciFiveChampionPoint : Real :=
  b ^ (-4 : Int) / (b ^ 2 - 1)

theorem five_root_bounds : 1 < b ∧ b < 2 := by
  exact ⟨one_lt_dbonacciPerronRoot 5 (by norm_num),
    dbonacciPerronRoot_lt_two 5 (by norm_num)⟩

theorem five_denominator_pos : 0 < b ^ 2 - 1 := by
  nlinarith [five_root_bounds.1]

theorem five_lowArm_pos : 0 < lowArm := by
  have hbphi : Real.goldenRatio < b := by
    rw [← dbonacciPerronRoot_two_eq_goldenRatio]
    exact dbonacciPerronRoot_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  have hphi := Real.goldenRatio_sq
  have hproduct :
      0 < (b - Real.goldenRatio) * (b + Real.goldenRatio - 1) := by
    exact mul_pos (sub_pos.mpr hbphi) (by nlinarith [Real.one_lt_goldenRatio])
  have hnum : 0 < b ^ 2 - b - 1 := by
    nlinarith
  exact div_pos hnum five_denominator_pos

theorem five_middleLeft_pos : 0 < middleLeft :=
  one_div_pos.mpr five_denominator_pos

theorem five_lowArm_lt_middleLeft : lowArm < middleLeft := by
  rw [div_lt_div_iff_of_pos_right five_denominator_pos]
  nlinarith [five_root_bounds.2, five_root_bounds.1]

theorem five_middleLeft_le_middleRight : middleLeft ≤ middleRight := by
  have htb : tribonacciConstant < b := by
    rw [← dbonacciPerronRoot_three_eq_tribonacciConstant]
    exact dbonacciPerronRoot_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  have hbquad : 0 < b ^ 2 - b := by
    nlinarith [five_root_bounds.1]
  have hcross : 0 < b * tribonacciConstant - 1 := by
    nlinarith [five_root_bounds.1, one_lt_tribonacciConstant,
      mul_pos (lt_trans zero_lt_one five_root_bounds.1)
        (lt_trans zero_lt_one one_lt_tribonacciConstant)]
  have htquad : 0 < tribonacciConstant ^ 2 - tribonacciConstant := by
    nlinarith [one_lt_tribonacciConstant]
  have hfactor :
      0 < (b - tribonacciConstant) *
        (b ^ 2 + b * tribonacciConstant + tribonacciConstant ^ 2 -
          b - tribonacciConstant - 1) := by
    apply mul_pos (sub_pos.mpr htb)
    nlinarith
  have hcubic := tribonacciConstant_cubic
  have hnum : 0 < b ^ 3 - b ^ 2 - b - 1 := by
    nlinarith
  have hdifference :
      middleRight - middleLeft =
        (b ^ 3 - b ^ 2 - b - 1) / (b ^ 2 - 1) := by
    field_simp [five_denominator_pos.ne']
  rw [← sub_nonneg, hdifference]
  exact div_nonneg hnum.le five_denominator_pos.le

theorem five_lowArm_lt_largeLeft : lowArm < largeLeft := by
  exact five_lowArm_lt_middleLeft.trans (by
    apply div_lt_div_of_pos_right
    · exact five_root_bounds.1
    · exact five_denominator_pos)

theorem five_coordinate_sum : largeLeft + lowArm = 1 := by
  field_simp [five_denominator_pos.ne']
  ring

theorem five_large_branch : b * largeLeft - 1 = middleLeft := by
  field_simp [five_denominator_pos.ne']
  ring

theorem five_middle_branch : b * middleLeft = largeLeft := by
  field_simp [five_denominator_pos.ne']

theorem five_middle_complement : 1 - b * middleLeft = lowArm := by
  rw [five_middle_branch]
  nlinarith [five_coordinate_sum]

theorem five_scale_succ (Q : Nat) :
    b ^ (-(Q : Int)) = b * b ^ (-((Q + 1 : Nat) : Int)) := by
  calc
    b ^ (-(Q : Int)) = b ^ ((1 : Int) + -((Q + 1 : Nat) : Int)) := by
      congr 1
      push_cast
      omega
    _ = b ^ (1 : Int) * b ^ (-((Q + 1 : Nat) : Int)) := by
      rw [zpow_add₀ (ne_of_gt (zero_lt_one.trans five_root_bounds.1))]
    _ = b * b ^ (-((Q + 1 : Nat) : Int)) := by rw [zpow_one]

theorem five_top_gap_length (Q : Nat) :
    dbonacciGapLength 5 Q 4 = b ^ (-(Q : Int)) := by
  unfold dbonacciGapLength
  have hfull : dbonacciBudgetBound 5 4 = 1 := by
    simpa using dbonacciBudgetBound_full 5 (by norm_num)
  rw [hfull, mul_one, zpow_neg, zpow_natCast, inv_pow]

/-- The largest labeled phase takes its right child into a label-three gap. -/
theorem five_large_to_middle (Q : Nat)
    (hgap : IsDBonacciOrbitGap 5 Q dbonacciFiveChampionPoint 4
      largeLeft lowArm) :
    IsDBonacciOrbitGap 5 (Q + 1) dbonacciFiveChampionPoint 3
      middleLeft middleRight := by
  rcases hgap with ⟨i, hlength, hleft, hright⟩
  obtain ⟨j, hset, hjleft, hjright⟩ :=
    positive_gap_substitution 5 Q 3 (by norm_num) i (by simpa using hlength)
  have hpositions := inserted_singleton_positions 5 Q i j hset
  let next : Fin (dbonacci 5 ((Q + 1) + 2) - 1) :=
    ⟨j.1, by
      change j.1 < dbonacci 5 (Q + 3) - 1
      have hrightbound := (levelEmbedding 5 Q (gapRight 5 Q i)).2
      omega⟩
  have hnextLeft : gapLeft 5 (Q + 1) next = j := by
    apply Fin.ext
    rfl
  have hnextRight :
      gapRight 5 (Q + 1) next = levelEmbedding 5 Q (gapRight 5 Q i) := by
    apply Fin.ext
    exact hpositions.2
  refine ⟨next, ?_, ?_, ?_⟩
  · rw [hnextLeft, hnextRight, levelEmbedding_value]
    exact hjright
  · rw [hnextLeft]
    calc
      dbonacciFiveChampionPoint - indexedNameValue 5 (Q + 1) j =
          (dbonacciFiveChampionPoint - indexedNameValue 5 Q (gapLeft 5 Q i)) -
            (indexedNameValue 5 (Q + 1) j -
              indexedNameValue 5 Q (gapLeft 5 Q i)) := by ring
      _ = largeLeft * b ^ (-(Q : Int)) -
          b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [hleft, hjleft, five_top_gap_length]
      _ = (b * largeLeft - 1) * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [five_scale_succ Q]
            ring
      _ = middleLeft * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [five_large_branch]
  · rw [hnextRight, levelEmbedding_value]
    calc
      indexedNameValue 5 Q (gapRight 5 Q i) - dbonacciFiveChampionPoint =
          lowArm * b ^ (-(Q : Int)) := hright
      _ = middleRight * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [five_scale_succ Q]
            ring

/-- The label-three phase takes its left child back to the largest gap. -/
theorem five_middle_to_large (Q : Nat)
    (hgap : IsDBonacciOrbitGap 5 Q dbonacciFiveChampionPoint 3
      middleLeft middleRight) :
    IsDBonacciOrbitGap 5 (Q + 1) dbonacciFiveChampionPoint 4
      largeLeft lowArm := by
  rcases hgap with ⟨i, hlength, hleft, hright⟩
  obtain ⟨j, hset, hjleft, _⟩ :=
    positive_gap_substitution 5 Q 2 (by norm_num) i (by simpa using hlength)
  have hpositions := inserted_singleton_positions 5 Q i j hset
  let next : Fin (dbonacci 5 ((Q + 1) + 2) - 1) :=
    ⟨(levelEmbedding 5 Q (gapLeft 5 Q i)).1, by
      change (levelEmbedding 5 Q (gapLeft 5 Q i)).1 < dbonacci 5 (Q + 3) - 1
      have hjbound := j.2
      omega⟩
  have hnextLeft :
      gapLeft 5 (Q + 1) next = levelEmbedding 5 Q (gapLeft 5 Q i) := by
    apply Fin.ext
    rfl
  have hnextRight : gapRight 5 (Q + 1) next = j := by
    apply Fin.ext
    exact hpositions.1
  refine ⟨next, ?_, ?_, ?_⟩
  · rw [hnextLeft, hnextRight, levelEmbedding_value]
    exact hjleft
  · rw [hnextLeft, levelEmbedding_value]
    calc
      dbonacciFiveChampionPoint - indexedNameValue 5 Q (gapLeft 5 Q i) =
          middleLeft * b ^ (-(Q : Int)) := hleft
      _ = largeLeft * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [five_scale_succ Q]
            calc
              middleLeft * (b * b ^ (-((Q + 1 : Nat) : Int))) =
                  (b * middleLeft) * b ^ (-((Q + 1 : Nat) : Int)) := by ring
              _ = largeLeft * b ^ (-((Q + 1 : Nat) : Int)) := by
                rw [five_middle_branch]
  · rw [hnextRight]
    calc
      indexedNameValue 5 (Q + 1) j - dbonacciFiveChampionPoint =
          (indexedNameValue 5 (Q + 1) j -
              indexedNameValue 5 Q (gapLeft 5 Q i)) -
            (dbonacciFiveChampionPoint - indexedNameValue 5 Q (gapLeft 5 Q i)) := by
              ring
      _ = b ^ (-((Q + 1 : Nat) : Int)) -
          middleLeft * b ^ (-(Q : Int)) := by
            rw [hjleft, five_top_gap_length, hleft]
      _ = (1 - b * middleLeft) * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [five_scale_succ Q]
            ring
      _ = lowArm * b ^ (-((Q + 1 : Nat) : Int)) := by
            rw [five_middle_complement]

theorem dbonacci_five_seven_eq : dbonacci 5 7 = 31 := by
  rw [show 7 = 5 + 2 by omega, dbonacci_add_two_of_le 5 5 (by omega),
    Finset.sum_fin_eq_sum_range]
  norm_num [Finset.sum_range_succ, dbonacci_add_two_of_lt]

theorem five_short_bounded_card (Q : Nat) (hQ : Q < 5) :
    Fintype.card (BoundedRunName 4 4 Q) = 2 ^ Q := by
  rw [← dbonacci_name_card_eq_bounded 4 Q, dbonacci_name_card_of_lt 5 Q hQ]

theorem five_first_index_zero :
    indexedNameValue 5 5 ⟨0, by rw [dbonacci_five_seven_eq]; omega⟩ = 0 := by
  rw [indexedNameValue_succ_eq_bounded]
  have hindex :
      Fin.cast
          ((dbonacci_name_card 5 5).symm.trans
            (dbonacci_name_card_eq_bounded 4 5))
          ⟨0, by rw [dbonacci_five_seven_eq]; omega⟩ =
        ⟨0, bounded_run_level_pos 4 4 5⟩ := by
    apply Fin.ext
    rfl
  rw [hindex, boundedIndexedNameValue_zero]

theorem five_first_index_one :
    indexedNameValue 5 5 ⟨1, by rw [dbonacci_five_seven_eq]; omega⟩ =
      b ^ (-5 : Int) := by
  rw [indexedNameValue_succ_eq_bounded]
  let i5 := Fin.cast
    ((dbonacci_name_card 5 5).symm.trans (dbonacci_name_card_eq_bounded 4 5))
      (⟨1, by rw [dbonacci_five_seven_eq]; omega⟩ : Fin (dbonacci 5 7))
  have hi5 : i5.1 < Fintype.card (BoundedRunName 4 4 4) := by
    have hcard : 1 < Fintype.card (BoundedRunName 4 4 4) := by
      rw [five_short_bounded_card 4 (by omega)]
      norm_num
    simpa only [i5, Fin.val_cast] using hcard
  rw [show Fin.cast
      ((dbonacci_name_card 5 5).symm.trans (dbonacci_name_card_eq_bounded 4 5))
        (⟨1, by rw [dbonacci_five_seven_eq]; omega⟩ : Fin (dbonacci 5 7)) = i5
      by rfl,
    boundedIndexedNameValue_lower 4 3 4 i5 hi5]
  let i4 : Fin (Fintype.card (BoundedRunName 4 4 4)) := ⟨i5.1, hi5⟩
  have hi4 : i4.1 < Fintype.card (BoundedRunName 4 4 3) := by
    have hcard : 1 < Fintype.card (BoundedRunName 4 4 3) := by
      rw [five_short_bounded_card 3 (by omega)]
      norm_num
    simpa only [i4, i5, Fin.val_cast] using hcard
  rw [show (⟨i5.1, hi5⟩ : Fin (Fintype.card (BoundedRunName 4 4 4))) = i4 by rfl,
    boundedIndexedNameValue_lower 4 3 3 i4 hi4]
  let i3 : Fin (Fintype.card (BoundedRunName 4 4 3)) := ⟨i4.1, hi4⟩
  have hi3 : i3.1 < Fintype.card (BoundedRunName 4 4 2) := by
    have hcard : 1 < Fintype.card (BoundedRunName 4 4 2) := by
      rw [five_short_bounded_card 2 (by omega)]
      norm_num
    simpa only [i3, i4, i5, Fin.val_cast] using hcard
  rw [show (⟨i4.1, hi4⟩ : Fin (Fintype.card (BoundedRunName 4 4 3))) = i3 by rfl,
    boundedIndexedNameValue_lower 4 3 2 i3 hi3]
  let i2 : Fin (Fintype.card (BoundedRunName 4 4 2)) := ⟨i3.1, hi3⟩
  have hi2 : i2.1 < Fintype.card (BoundedRunName 4 4 1) := by
    have hcard : 1 < Fintype.card (BoundedRunName 4 4 1) := by
      rw [five_short_bounded_card 1 (by omega)]
      norm_num
    simpa only [i2, i3, i4, i5, Fin.val_cast] using hcard
  rw [show (⟨i3.1, hi3⟩ : Fin (Fintype.card (BoundedRunName 4 4 2))) = i2 by rfl,
    boundedIndexedNameValue_lower 4 3 1 i2 hi2]
  let i1 : Fin (Fintype.card (BoundedRunName 4 4 1)) := ⟨i2.1, hi2⟩
  have hi1 : Fintype.card (BoundedRunName 4 4 0) ≤ i1.1 := by
    have hcard : Fintype.card (BoundedRunName 4 4 0) ≤ 1 := by
      rw [five_short_bounded_card 0 (by omega)]
      norm_num
    simpa only [i1, i2, i3, i4, i5, Fin.val_cast] using hcard
  rw [show (⟨i2.1, hi2⟩ : Fin (Fintype.card (BoundedRunName 4 4 1))) = i1 by rfl,
    boundedIndexedNameValue_upper 4 3 0 i1 hi1]
  have hi1val : i1.1 = 1 := by
    simp only [i1, i2, i3, i4, i5, Fin.val_cast]
  have hcardFullZero : Fintype.card (BoundedRunName 4 4 0) = 1 := by
    rw [five_short_bounded_card 0 (by omega)]
    norm_num
  have hzero :
      boundedIndexedNameValue 4 3 0
          ⟨i1.1 - Fintype.card (BoundedRunName 4 4 0), by
            rw [hi1val, hcardFullZero]
            exact bounded_run_level_pos 4 3 0⟩ = 0 := by
    have hindex :
        (⟨i1.1 - Fintype.card (BoundedRunName 4 4 0), by
            rw [hi1val, hcardFullZero]
            exact bounded_run_level_pos 4 3 0⟩ :
          Fin (Fintype.card (BoundedRunName 4 3 0))) =
        ⟨0, bounded_run_level_pos 4 3 0⟩ := by
      apply Fin.ext
      change i1.1 - Fintype.card (BoundedRunName 4 4 0) = 0
      omega
    rw [hindex, boundedIndexedNameValue_zero]
  rw [hzero]
  simp only [mul_zero, add_zero]
  change b⁻¹ * (b⁻¹ * (b⁻¹ * (b⁻¹ * b⁻¹))) = b ^ (-5 : Int)
  rw [zpow_neg]
  calc
    b⁻¹ * (b⁻¹ * (b⁻¹ * (b⁻¹ * b⁻¹))) = b⁻¹ ^ 5 := by ring
    _ = (b ^ 5)⁻¹ := inv_pow b 5

theorem five_champion_point_scaled :
    dbonacciFiveChampionPoint = largeLeft * b ^ (-5 : Int) := by
  unfold dbonacciFiveChampionPoint
  have hscale : b ^ (-4 : Int) = b * b ^ (-5 : Int) := by
    calc
      b ^ (-4 : Int) = b ^ ((1 : Int) + (-5 : Int)) := by norm_num
      _ = b ^ (1 : Int) * b ^ (-5 : Int) := by
        rw [zpow_add₀ (ne_of_gt (zero_lt_one.trans five_root_bounds.1))]
      _ = b * b ^ (-5 : Int) := by rw [zpow_one]
  rw [hscale]
  ring

/-- The closed point starts in the first level-five largest gap. -/
theorem five_champion_base_gap :
    IsDBonacciOrbitGap 5 5 dbonacciFiveChampionPoint 4 largeLeft lowArm := by
  let i : Fin (dbonacci 5 (5 + 2) - 1) :=
    ⟨0, by rw [dbonacci_five_seven_eq]; omega⟩
  have hleft : gapLeft 5 5 i =
      (⟨0, by rw [dbonacci_five_seven_eq]; omega⟩ : Fin (dbonacci 5 7)) := by
    apply Fin.ext
    rfl
  have hright : gapRight 5 5 i =
      (⟨1, by rw [dbonacci_five_seven_eq]; omega⟩ : Fin (dbonacci 5 7)) := by
    apply Fin.ext
    rfl
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [hleft, hright, five_first_index_zero, five_first_index_one, sub_zero]
    exact (five_top_gap_length 5).symm
  · rw [hleft, five_first_index_zero, sub_zero]
    exact five_champion_point_scaled
  · rw [hright, five_first_index_one, five_champion_point_scaled]
    calc
      b ^ (-5 : Int) - largeLeft * b ^ (-5 : Int) =
          (1 - largeLeft) * b ^ (-5 : Int) := by ring
      _ = lowArm * b ^ (-5 : Int) := by
            rw [show 1 - largeLeft = lowArm by nlinarith [five_coordinate_sum]]

/-- The containing five-bonacci gap has exact right-left period two. -/
theorem five_champion_gap_orbit (k : Nat) :
    IsDBonacciOrbitGap 5 (2 * k + 5) dbonacciFiveChampionPoint 4
        largeLeft lowArm ∧
      IsDBonacciOrbitGap 5 (2 * k + 6) dbonacciFiveChampionPoint 3
        middleLeft middleRight := by
  induction k with
  | zero =>
      have hlarge := five_champion_base_gap
      refine ⟨?_, ?_⟩
      · simpa using hlarge
      · simpa using five_large_to_middle 5 hlarge
  | succ k ih =>
      have hlarge := five_middle_to_large (2 * k + 6) ih.2
      have hmiddle := five_large_to_middle (2 * k + 7) hlarge
      constructor
      · convert hlarge using 1
        omega
      · convert hmiddle using 1
        omega

theorem five_champion_survivor_even (k : Nat) :
    dbonacciSurvivor 5 (2 * k + 5) dbonacciFiveChampionPoint = lowArm := by
  apply dbonacciSurvivor_eq_of_orbit_gap 5 (2 * k + 5) (by norm_num)
      (hgap := (five_champion_gap_orbit k).1)
  · exact (div_pos (zero_lt_one.trans five_root_bounds.1) five_denominator_pos).le
  · exact five_lowArm_pos.le
  · exact five_lowArm_lt_largeLeft.le
  · exact le_rfl
  · exact Or.inr rfl

theorem five_champion_survivor_odd (k : Nat) :
    dbonacciSurvivor 5 (2 * k + 6) dbonacciFiveChampionPoint = middleLeft := by
  apply dbonacciSurvivor_eq_of_orbit_gap 5 (2 * k + 6) (by norm_num)
      (hgap := (five_champion_gap_orbit k).2)
  · exact five_middleLeft_pos.le
  · exact mul_nonneg (zero_le_one.trans five_root_bounds.1.le) five_lowArm_pos.le
  · exact le_rfl
  · exact five_middleLeft_le_middleRight
  · exact Or.inl rfl

/-- The five-bonacci period-two point has the corrected champion liminf. -/
theorem dbonacci_five_champion_liminf :
    Filter.liminf (fun Q => dbonacciSurvivor 5 Q dbonacciFiveChampionPoint)
        Filter.atTop = championValue b := by
  change Filter.liminf (fun Q => dbonacciSurvivor 5 Q dbonacciFiveChampionPoint)
      Filter.atTop = lowArm
  have heventually_lower :
      ∀ᶠ Q in Filter.atTop,
        lowArm ≤ dbonacciSurvivor 5 Q dbonacciFiveChampionPoint := by
    rw [Filter.eventually_atTop]
    refine ⟨5, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 5 := ⟨Q - 5, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [five_champion_survivor_even]
    · subst n
      rw [show (2 * k + 1) + 5 = 2 * k + 6 by omega,
        five_champion_survivor_odd]
      exact five_lowArm_lt_middleLeft.le
  have heventually_upper :
      ∀ᶠ Q in Filter.atTop,
        dbonacciSurvivor 5 Q dbonacciFiveChampionPoint ≤ middleLeft := by
    rw [Filter.eventually_atTop]
    refine ⟨5, ?_⟩
    intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 5 := ⟨Q - 5, by omega⟩
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      rw [five_champion_survivor_even]
      exact five_lowArm_lt_middleLeft.le
    · subst n
      rw [show (2 * k + 1) + 5 = 2 * k + 6 by omega,
        five_champion_survivor_odd]
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨2 * N + 5, by omega, ?_⟩
      rw [five_champion_survivor_even]
    · exact ⟨lowArm, heventually_lower⟩
  · exact Filter.le_liminf_of_le
      (Filter.IsBoundedUnder.isCoboundedUnder_ge ⟨middleLeft, heventually_upper⟩)
      heventually_lower

/-- The five-bonacci champion liminf agrees with `0.313794` within one millionth. -/
theorem dbonacci_five_champion_liminf_numeric :
    |Filter.liminf (fun Q => dbonacciSurvivor 5 Q dbonacciFiveChampionPoint)
        Filter.atTop - (313794 : Real) / 1000000| < (1 : Real) / 1000000 := by
  rw [dbonacci_five_champion_liminf]
  exact championValue_five_numeric

/-- The initial expression does not equal the five-bonacci champion liminf. -/
theorem dbonacci_five_initial_formula_ne_champion_liminf :
    (1 - b⁻¹) / 2 ≠
      Filter.liminf (fun Q => dbonacciSurvivor 5 Q dbonacciFiveChampionPoint)
        Filter.atTop := by
  rw [dbonacci_five_champion_liminf]
  exact dbonacci_five_initial_formula_ne_championValue

end D5.S0.Tower.DBonacciGeneral.FiveChampionOrbit
