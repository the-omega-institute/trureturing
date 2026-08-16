/- GID: D5/S0/Tower/DBonacciGeneral/ChampionValue
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/ChampionValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The corrected d-bonacci champion value has exact low-order and endpoint checks. -/

import D5.S0.Tower.DBonacci.PerronRoot
import D5.S0.Tower.Tribonacci.ChampionOrbit

namespace D5.S0.Tower.DBonacciGeneral.ChampionValue

open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.Tribonacci.ChampionOrbit
open D5.S0.Tower.Tribonacci.Survivor
open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant
local notation "phi" => Real.goldenRatio

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen Tribonacci champion liminf and the
     general d-bonacci Perron-root bridges at orders two and three.
   * Pinned mathlib supplies `Real.goldenRatio_sq`; no duplicate algebraic
     proof or third-party dependency is introduced. -/

/-- The corrected algebraic champion value. Its champion interpretation is
used only for d-bonacci orders `d >= 3`; at order two this expression is zero
and does not state the separate degenerate-phase value. -/
noncomputable def championValue (beta : Real) : Real :=
  (beta ^ 2 - beta - 1) / (beta ^ 2 - 1)

/-- At the Tribonacci root, the corrected value equals the frozen low arm. -/
theorem championValue_tribonacciConstant :
    championValue t = (1 - t⁻¹) / 2 := by
  have ht_ne : t ≠ 0 := tribonacciConstant_ne_zero
  have hden_ne : t ^ 2 - 1 ≠ 0 := by
    nlinarith [one_lt_tribonacciConstant]
  unfold championValue
  field_simp [ht_ne, hden_ne]
  nlinarith [tribonacciConstant_cubic]

/-- The frozen Tribonacci champion liminf is the corrected value at `t`. -/
theorem tribonacci_champion_liminf_eq_championValue :
    Filter.liminf (fun Q => tribonacciSurvivor Q tribonacciChampionPoint)
        Filter.atTop = championValue t := by
  rw [tribonacci_champion_liminf, championValue_tribonacciConstant]
  simp [zpow_neg]

/-- The order-two numerator vanishes by the golden-ratio quadratic equation. -/
theorem goldenRatio_championValue_numerator :
    phi ^ 2 - phi - 1 = 0 := by
  nlinarith [Real.goldenRatio_sq]

/-- The corrected expression evaluates to zero at the order-two root.
This is not a claim about the separate degenerate-phase champion value. -/
theorem championValue_goldenRatio : championValue phi = 0 := by
  rw [championValue, goldenRatio_championValue_numerator]
  norm_num

/-- Direct substitution at the limiting endpoint gives the welded value `1/3`. -/
theorem championValue_two : championValue 2 = (1 : Real) / 3 := by
  norm_num [championValue]

/-- Above one, the initial expression agrees with the corrected value exactly
on roots of the Tribonacci cubic. -/
theorem initialFormula_eq_championValue_iff {beta : Real} (hbeta : 1 < beta) :
    (1 - beta⁻¹) / 2 = championValue beta ↔
      beta ^ 3 = beta ^ 2 + beta + 1 := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt (lt_trans zero_lt_one hbeta)
  have hden_ne : beta ^ 2 - 1 ≠ 0 := by
    nlinarith
  constructor
  · intro heq
    unfold championValue at heq
    field_simp [hbeta_ne, hden_ne] at heq
    nlinarith
  · intro hcubic
    unfold championValue
    field_simp [hbeta_ne, hden_ne]
    nlinarith

/-- The initial expression and corrected value differ at the order-five root. -/
theorem dbonacci_five_initial_formula_ne_championValue :
    (1 - (dbonacciPerronRoot 5)⁻¹) / 2 ≠
      championValue (dbonacciPerronRoot 5) := by
  intro heq
  have hfive_gt_one : 1 < dbonacciPerronRoot 5 :=
    one_lt_dbonacciPerronRoot 5 (by norm_num)
  have hcubic :
      dbonacciPerronRoot 5 ^ 3 =
        dbonacciPerronRoot 5 ^ 2 + dbonacciPerronRoot 5 + 1 :=
    (initialFormula_eq_championValue_iff hfive_gt_one).mp heq
  have heq_t : dbonacciPerronRoot 5 = t :=
    D5.S0.Tower.Tribonacci.PerronRoot.eq_tribonacciConstant_of_one_lt
      hfive_gt_one hcubic
  have hthree_five : dbonacciPerronRoot 3 < dbonacciPerronRoot 5 :=
    dbonacciPerronRoot_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  rw [dbonacciPerronRoot_three_eq_tribonacciConstant, ← heq_t] at hthree_five
  exact lt_irrefl _ hthree_five

/-- A rational test point with reciprocal sum above one lies below the root. -/
theorem lt_dbonacciPerronRoot_of_one_lt_reciprocalSum (d : Nat) (hd : 2 ≤ d)
    {q : Real} (hq : 0 < q) (hsum : 1 < dbonacciReciprocalSum d q) :
    q < dbonacciPerronRoot d := by
  by_contra hnot
  have hroot_le : dbonacciPerronRoot d ≤ q := le_of_not_gt hnot
  rcases hroot_le.eq_or_lt with heq | hlt
  · rw [← heq, dbonacciPerronRoot_reciprocalSum d hd] at hsum
    exact lt_irrefl 1 hsum
  · have hanti := dbonacci_reciprocalSum_strictAntiOn d (by omega)
    have hslt := hanti
      (show dbonacciPerronRoot d ∈ Set.Ioi (0 : Real) from
        lt_trans zero_lt_one (one_lt_dbonacciPerronRoot d hd))
      (show q ∈ Set.Ioi (0 : Real) from hq) hlt
    rw [dbonacciPerronRoot_reciprocalSum d hd] at hslt
    linarith

/-- A rational test point with reciprocal sum below one lies above the root. -/
theorem dbonacciPerronRoot_lt_of_reciprocalSum_lt_one (d : Nat) (hd : 2 ≤ d)
    {q : Real} (hq : 0 < q) (hsum : dbonacciReciprocalSum d q < 1) :
    dbonacciPerronRoot d < q := by
  by_contra hnot
  have hq_le : q ≤ dbonacciPerronRoot d := le_of_not_gt hnot
  rcases hq_le.eq_or_lt with heq | hlt
  · rw [heq, dbonacciPerronRoot_reciprocalSum d hd] at hsum
    exact lt_irrefl 1 hsum
  · have hanti := dbonacci_reciprocalSum_strictAntiOn d (by omega)
    have hslt := hanti
      (show q ∈ Set.Ioi (0 : Real) from hq)
      (show dbonacciPerronRoot d ∈ Set.Ioi (0 : Real) from
        lt_trans zero_lt_one (one_lt_dbonacciPerronRoot d hd)) hlt
    rw [dbonacciPerronRoot_reciprocalSum d hd] at hslt
    linarith

/-- The corrected value is strictly increasing throughout its champion domain. -/
theorem championValue_strictMonoOn :
    StrictMonoOn championValue (Set.Ioi (1 : Real)) := by
  intro x hx y hy hxy
  have hx_one : 1 < x := hx
  have hy_one : 1 < y := hy
  have hxd : 0 < x ^ 2 - 1 := by
    have := mul_pos (sub_pos.mpr hx_one) (by nlinarith : 0 < x + 1)
    nlinarith
  have hyd : 0 < y ^ 2 - 1 := by
    have := mul_pos (sub_pos.mpr hy_one) (by nlinarith : 0 < y + 1)
    nlinarith
  have hxy_pos : 0 < x * y + 1 := by
    nlinarith [mul_pos (lt_trans zero_lt_one hx_one) (lt_trans zero_lt_one hy_one)]
  have hproduct : 0 < (y - x) * (x * y + 1) :=
    mul_pos (sub_pos.mpr hxy) hxy_pos
  simp only [championValue]
  rw [div_lt_div_iff₀ hxd hyd]
  nlinarith

/-- Millionth-scale rational enclosure of the order-three Perron root. -/
theorem dbonacci_three_root_numeric_bounds :
    (1839286 : Real) / 1000000 < dbonacciPerronRoot 3 ∧
      dbonacciPerronRoot 3 < (1839287 : Real) / 1000000 := by
  constructor
  · apply lt_dbonacciPerronRoot_of_one_lt_reciprocalSum 3 (by norm_num)
    · norm_num
    · norm_num [dbonacciReciprocalSum, Finset.sum_range_succ]
  · apply dbonacciPerronRoot_lt_of_reciprocalSum_lt_one 3 (by norm_num)
    · norm_num
    · norm_num [dbonacciReciprocalSum, Finset.sum_range_succ]

/-- Millionth-scale rational enclosure of the order-four Perron root. -/
theorem dbonacci_four_root_numeric_bounds :
    (1927561 : Real) / 1000000 < dbonacciPerronRoot 4 ∧
      dbonacciPerronRoot 4 < (1927562 : Real) / 1000000 := by
  constructor
  · apply lt_dbonacciPerronRoot_of_one_lt_reciprocalSum 4 (by norm_num)
    · norm_num
    · norm_num [dbonacciReciprocalSum, Finset.sum_range_succ]
  · apply dbonacciPerronRoot_lt_of_reciprocalSum_lt_one 4 (by norm_num)
    · norm_num
    · norm_num [dbonacciReciprocalSum, Finset.sum_range_succ]

/-- Millionth-scale rational enclosure of the order-five Perron root. -/
theorem dbonacci_five_root_numeric_bounds :
    (1965948 : Real) / 1000000 < dbonacciPerronRoot 5 ∧
      dbonacciPerronRoot 5 < (1965949 : Real) / 1000000 := by
  constructor
  · apply lt_dbonacciPerronRoot_of_one_lt_reciprocalSum 5 (by norm_num)
    · norm_num
    · norm_num [dbonacciReciprocalSum, Finset.sum_range_succ]
  · apply dbonacciPerronRoot_lt_of_reciprocalSum_lt_one 5 (by norm_num)
    · norm_num
    · norm_num [dbonacciReciprocalSum, Finset.sum_range_succ]

/-- The order-three value agrees with `0.228155` to within one millionth. -/
theorem championValue_three_numeric :
    |championValue (dbonacciPerronRoot 3) - (228155 : Real) / 1000000| <
      (1 : Real) / 1000000 := by
  have hmono := championValue_strictMonoOn
  have hl : (228154 : Real) / 1000000 < championValue (dbonacciPerronRoot 3) :=
    calc
      (228154 : Real) / 1000000 < championValue ((1839286 : Real) / 1000000) := by
        norm_num [championValue]
      _ < championValue (dbonacciPerronRoot 3) :=
        hmono (by norm_num) (one_lt_dbonacciPerronRoot 3 (by norm_num))
          dbonacci_three_root_numeric_bounds.1
  have hu : championValue (dbonacciPerronRoot 3) < (228156 : Real) / 1000000 :=
    calc
      championValue (dbonacciPerronRoot 3) <
          championValue ((1839287 : Real) / 1000000) :=
        hmono (one_lt_dbonacciPerronRoot 3 (by norm_num)) (by norm_num)
          dbonacci_three_root_numeric_bounds.2
      _ < (228156 : Real) / 1000000 := by norm_num [championValue]
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

/-- The order-four value agrees with `0.290162` to within one millionth. -/
theorem championValue_four_numeric :
    |championValue (dbonacciPerronRoot 4) - (290162 : Real) / 1000000| <
      (1 : Real) / 1000000 := by
  have hmono := championValue_strictMonoOn
  have hl : (290161 : Real) / 1000000 < championValue (dbonacciPerronRoot 4) :=
    calc
      (290161 : Real) / 1000000 < championValue ((1927561 : Real) / 1000000) := by
        norm_num [championValue]
      _ < championValue (dbonacciPerronRoot 4) :=
        hmono (by norm_num) (one_lt_dbonacciPerronRoot 4 (by norm_num))
          dbonacci_four_root_numeric_bounds.1
  have hu : championValue (dbonacciPerronRoot 4) < (290163 : Real) / 1000000 :=
    calc
      championValue (dbonacciPerronRoot 4) <
          championValue ((1927562 : Real) / 1000000) :=
        hmono (one_lt_dbonacciPerronRoot 4 (by norm_num)) (by norm_num)
          dbonacci_four_root_numeric_bounds.2
      _ < (290163 : Real) / 1000000 := by norm_num [championValue]
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

/-- The order-five value agrees with `0.313794` to within one millionth. -/
theorem championValue_five_numeric :
    |championValue (dbonacciPerronRoot 5) - (313794 : Real) / 1000000| <
      (1 : Real) / 1000000 := by
  have hmono := championValue_strictMonoOn
  have hl : (313793 : Real) / 1000000 < championValue (dbonacciPerronRoot 5) :=
    calc
      (313793 : Real) / 1000000 < championValue ((1965948 : Real) / 1000000) := by
        norm_num [championValue]
      _ < championValue (dbonacciPerronRoot 5) :=
        hmono (by norm_num) (one_lt_dbonacciPerronRoot 5 (by norm_num))
          dbonacci_five_root_numeric_bounds.1
  have hu : championValue (dbonacciPerronRoot 5) < (313795 : Real) / 1000000 :=
    calc
      championValue (dbonacciPerronRoot 5) <
          championValue ((1965949 : Real) / 1000000) :=
        hmono (one_lt_dbonacciPerronRoot 5 (by norm_num)) (by norm_num)
          dbonacci_five_root_numeric_bounds.2
      _ < (313795 : Real) / 1000000 := by norm_num [championValue]
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

end D5.S0.Tower.DBonacciGeneral.ChampionValue
