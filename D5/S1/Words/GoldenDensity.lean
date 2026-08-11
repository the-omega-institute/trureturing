/- GID: D5/S1/Words/GoldenDensity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-symbolic-density-theorems)
   anchors: []
   digest: Golden-word true counts have discrepancy below one and density inverse golden ratio. -/

import D5.S1.Words.GoldenBalance

namespace D5.S1.Words

/-- Every golden-word window has true-count discrepancy strictly below one. -/
theorem golden_window_true_discrepancy (i n : Nat) :
    |(goldenWindowTrueCount i n : Real) - n * Real.goldenRatio⁻¹| < 1 := by
  let x : Real := ((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹
  let t : Real := (n : Real) * Real.goldenRatio⁻¹
  have hendpoint :
      (((i + n + 1 : Nat) : Real) * Real.goldenRatio⁻¹) = x + t := by
    dsimp [x, t]
    push_cast
    ring
  have hcount_int := goldenWindowTrueCount_eq_floor i n
  rw [hendpoint] at hcount_int
  have hcount :
      (goldenWindowTrueCount i n : Real) =
        ((⌊x + t⌋ : Int) : Real) - ((⌊x⌋ : Int) : Real) := by
    exact_mod_cast hcount_int
  have herror :
      (goldenWindowTrueCount i n : Real) - t = Int.fract x - Int.fract (x + t) := by
    rw [hcount]
    linarith [Int.floor_add_fract x, Int.floor_add_fract (x + t)]
  change |(goldenWindowTrueCount i n : Real) - t| < 1
  rw [herror, abs_lt]
  constructor
  · linarith [Int.fract_nonneg x, Int.fract_lt_one (x + t)]
  · linarith [Int.fract_lt_one x, Int.fract_nonneg (x + t)]

/-- The true-letter density of every fixed golden-word window start tends to the inverse ratio. -/
theorem golden_word_window_true_density (i : Nat) :
    Filter.Tendsto (fun n : Nat => (goldenWindowTrueCount i n : Real) / n)
      Filter.atTop (nhds Real.goldenRatio⁻¹) := by
  let alpha : Real := Real.goldenRatio⁻¹
  have hzero :
      Filter.Tendsto (fun n : Nat => (1 : Real) / n) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlower :
      Filter.Tendsto (fun n : Nat => alpha - (1 : Real) / n)
        Filter.atTop (nhds alpha) := by
    simpa using tendsto_const_nhds.sub hzero
  have hupper :
      Filter.Tendsto (fun n : Nat => alpha + (1 : Real) / n)
        Filter.atTop (nhds alpha) := by
    simpa using tendsto_const_nhds.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
    have hn_pos : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hdisc := golden_window_true_discrepancy i n
    rw [abs_lt] at hdisc
    have hl : (n : Real) * alpha - 1 ≤ (goldenWindowTrueCount i n : Real) := by
      dsimp [alpha] at hdisc ⊢
      linarith
    calc
      alpha - (1 : Real) / n = ((n : Real) * alpha - 1) / n := by
        field_simp
      _ ≤ (goldenWindowTrueCount i n : Real) / n :=
        (div_le_div_iff_of_pos_right hn_pos).2 hl
  · filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
    have hn_pos : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hdisc := golden_window_true_discrepancy i n
    rw [abs_lt] at hdisc
    have hu : (goldenWindowTrueCount i n : Real) ≤ (n : Real) * alpha + 1 := by
      dsimp [alpha] at hdisc ⊢
      linarith
    calc
      (goldenWindowTrueCount i n : Real) / n ≤ ((n : Real) * alpha + 1) / n :=
        (div_le_div_iff_of_pos_right hn_pos).2 hu
      _ = alpha + (1 : Real) / n := by
        field_simp

/-- The prefix true-letter density of the golden word is the inverse golden ratio. -/
theorem golden_word_true_density :
    Filter.Tendsto (fun n : Nat => (goldenWindowTrueCount 0 n : Real) / n)
      Filter.atTop (nhds Real.goldenRatio⁻¹) :=
  golden_word_window_true_density 0

private theorem golden_true_count_examples :
    [goldenWindowTrueCount 0 10, goldenWindowTrueCount 0 100] = [6, 62] := by
  decide

#print axioms golden_window_true_discrepancy
#print axioms golden_word_window_true_density
#print axioms golden_word_true_density

end D5.S1.Words
