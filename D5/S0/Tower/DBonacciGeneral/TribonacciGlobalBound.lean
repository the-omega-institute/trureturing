/- GID: D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/TribonacciGlobalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The unrestricted real-line Tribonacci champion upper bound is false. -/

import D5.S0.Tower.DBonacciGeneral.ChampionValue

namespace D5.S0.Tower.DBonacciGeneral.TribonacciGlobalBound

open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.Tribonacci.Gaps
open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Survivor
open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen Tribonacci terminal-gap recurrence
     inside the three-gap proof and the analogous golden endpoint refutation.
   * Pinned mathlib supplies `Metric.le_infDist`, the filter liminf lemmas,
     and the elementary `Nat.mod_add_div` decomposition used below. No
     third-party endpoint or global-champion theorem was found or introduced. -/

/-- The terminal gap inherits the three-step scaling visible in the recursive
upper block of the canonical Tribonacci ordering. -/
theorem tribonacci_terminal_gap_add_three (Q : Nat) :
    tribonacciTerminalGap (Q + 3) =
      t ^ (-3 : Int) * tribonacciTerminalGap Q := by
  have htotal : tribonacci (Q + 5) =
      tribonacci (Q + 4) + (tribonacci (Q + 3) + tribonacci (Q + 2)) :=
    tribonacci_count_split Q
  have hlastUpper : tribonacci (Q + 4) + tribonacci (Q + 3) <=
      (tribonacciLastIndex (Q + 3)).1 := by
    simp only [tribonacciLastIndex]
    rw [htotal]
    have := tribonacci_level_pos Q
    omega
  have hresBound :
      (tribonacciLastIndex (Q + 3)).1 -
          (tribonacci (Q + 4) + tribonacci (Q + 3)) < tribonacci (Q + 2) := by
    simp only [tribonacciLastIndex]
    rw [htotal]
    have := tribonacci_level_pos Q
    omega
  have hresIndex :
      (⟨(tribonacciLastIndex (Q + 3)).1 -
          (tribonacci (Q + 4) + tribonacci (Q + 3)), hresBound⟩ :
          Fin (tribonacci (Q + 2))) = tribonacciLastIndex Q := by
    apply Fin.ext
    simp only [tribonacciLastIndex]
    rw [htotal]
    have := tribonacci_level_pos Q
    omega
  rw [tribonacciTerminalGap,
    indexedNameValue_upper Q (tribonacciLastIndex (Q + 3)) hlastUpper,
    hresIndex]
  have hfactor :
      1 - (t ^ (-1 : Int) + t ^ (-2 : Int) +
          t ^ (-3 : Int) * indexedNameValue Q (tribonacciLastIndex Q)) =
        t ^ (-3 : Int) * tribonacciTerminalGap Q := by
    unfold tribonacciTerminalGap
    linarith [tribonacci_inverse_sum]
  exact hfactor

theorem tribonacci_terminal_gap_zero : tribonacciTerminalGap 0 = 1 := by
  have hlast : tribonacciLastIndex 0 = ⟨0, by decide⟩ := by
    apply Fin.ext
    norm_num [tribonacciLastIndex, tribonacci]
  rw [tribonacciTerminalGap, hlast, indexedNameValue_level_zero]
  norm_num

theorem tribonacci_terminal_gap_one :
    tribonacciTerminalGap 1 = 1 - t ^ (-1 : Int) := by
  have hlast : tribonacciLastIndex 1 = ⟨1, by decide⟩ := by
    apply Fin.ext
    norm_num [tribonacciLastIndex, tribonacci]
  rw [tribonacciTerminalGap, hlast, indexedNameValue_level_one_one]

theorem tribonacci_terminal_gap_two :
    tribonacciTerminalGap 2 = t ^ (-3 : Int) := by
  have hlast : tribonacciLastIndex 2 = ⟨3, by decide⟩ := by
    apply Fin.ext
    norm_num [tribonacciLastIndex, tribonacci]
  rw [tribonacciTerminalGap, hlast, indexedNameValue_level_two_three]
  linarith [tribonacci_inverse_sum]

theorem tribonacci_terminal_gap_pos (Q : Nat) : 0 < tribonacciTerminalGap Q := by
  rcases (tribonacci_gap_invariant Q).2 with hlarge | hsmall | hcombined
  · rw [hlarge]
    exact zpow_pos tribonacciConstant_pos _
  · rw [hsmall]
    exact zpow_pos tribonacciConstant_pos _
  · rw [hcombined]
    exact add_pos (zpow_pos tribonacciConstant_pos _)
      (zpow_pos tribonacciConstant_pos _)

/-- At the omitted endpoint one, the nearest name is the final indexed name. -/
theorem tribonacci_infDist_one_eq_terminal (Q : Nat) :
    Metric.infDist 1 (tribonacciNameGrid Q) = tribonacciTerminalGap Q := by
  let last := tribonacciLastIndex Q
  have hlastMem : indexedNameValue Q last ∈ tribonacciNameGrid Q := ⟨last, rfl⟩
  have hgrid : (tribonacciNameGrid Q).Nonempty :=
    ⟨indexedNameValue Q last, hlastMem⟩
  apply le_antisymm
  · calc
      Metric.infDist 1 (tribonacciNameGrid Q) <=
          dist 1 (indexedNameValue Q last) :=
        Metric.infDist_le_dist_of_mem hlastMem
      _ = tribonacciTerminalGap Q := by
        rw [Real.dist_eq, abs_of_nonneg]
        · rfl
        · change 0 <= 1 - indexedNameValue Q last
          exact (tribonacci_terminal_gap_pos Q).le
  · rw [Metric.le_infDist hgrid]
    intro y hy
    rcases hy with ⟨j, rfl⟩
    have hjlast : j <= last := by
      change j.1 <= tribonacci (Q + 2) - 1
      have hj := j.2
      omega
    have hjvalue : indexedNameValue Q j <= indexedNameValue Q last :=
      (indexed_nameValue_strictMono Q).monotone hjlast
    have hlastOne : indexedNameValue Q last < 1 := by
      have hgap := tribonacci_terminal_gap_pos Q
      unfold tribonacciTerminalGap at hgap
      change indexedNameValue Q (tribonacciLastIndex Q) < 1
      linarith
    rw [Real.dist_eq, abs_of_nonneg]
    · change 1 - indexedNameValue Q last <= 1 - indexedNameValue Q j
      linarith
    · linarith

/-- Normalization cancels the terminal gap's three-step scaling. -/
theorem tribonacci_survivor_one_add_three (Q : Nat) :
    tribonacciSurvivor (Q + 3) 1 = tribonacciSurvivor Q 1 := by
  unfold tribonacciSurvivor
  rw [tribonacci_infDist_one_eq_terminal,
    tribonacci_infDist_one_eq_terminal, tribonacci_terminal_gap_add_three]
  calc
    t ^ ((Q + 3 : Nat) : Int) *
        (t ^ (-3 : Int) * tribonacciTerminalGap Q) =
      (t ^ ((Q + 3 : Nat) : Int) * t ^ (-3 : Int)) *
        tribonacciTerminalGap Q := by ring
    _ = t ^ (Q : Int) * tribonacciTerminalGap Q := by
      rw [← zpow_add₀ tribonacciConstant_ne_zero]
      congr 2
      push_cast
      omega

theorem tribonacci_survivor_one_zero : tribonacciSurvivor 0 1 = 1 := by
  unfold tribonacciSurvivor
  rw [tribonacci_infDist_one_eq_terminal, tribonacci_terminal_gap_zero]
  norm_num

theorem tribonacci_survivor_one_one : tribonacciSurvivor 1 1 = t - 1 := by
  unfold tribonacciSurvivor
  rw [tribonacci_infDist_one_eq_terminal, tribonacci_terminal_gap_one]
  norm_num only [Nat.cast_one, zpow_one, zpow_neg]
  field_simp [tribonacciConstant_ne_zero]

theorem tribonacci_survivor_one_two :
    tribonacciSurvivor 2 1 = t ^ (-1 : Int) := by
  unfold tribonacciSurvivor
  rw [tribonacci_infDist_one_eq_terminal, tribonacci_terminal_gap_two]
  change t ^ (2 : Int) * t ^ (-3 : Int) = t ^ (-1 : Int)
  rw [← zpow_add₀ tribonacciConstant_ne_zero]
  norm_num

theorem tribonacci_survivor_one_mod_zero (k : Nat) :
    tribonacciSurvivor (3 * k) 1 = 1 := by
  induction k with
  | zero => simpa using tribonacci_survivor_one_zero
  | succ k ih =>
      rw [show 3 * (k + 1) = 3 * k + 3 by omega,
        tribonacci_survivor_one_add_three, ih]

theorem tribonacci_survivor_one_mod_one (k : Nat) :
    tribonacciSurvivor (3 * k + 1) 1 = t - 1 := by
  induction k with
  | zero => simpa using tribonacci_survivor_one_one
  | succ k ih =>
      rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 3 by omega,
        tribonacci_survivor_one_add_three, ih]

theorem tribonacci_survivor_one_mod_two (k : Nat) :
    tribonacciSurvivor (3 * k + 2) 1 = t ^ (-1 : Int) := by
  induction k with
  | zero => simpa using tribonacci_survivor_one_two
  | succ k ih =>
      rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 by omega,
        tribonacci_survivor_one_add_three, ih]

theorem tribonacci_nat_mod_three (Q : Nat) :
    ∃ k : Nat, Q = 3 * k ∨ Q = 3 * k + 1 ∨ Q = 3 * k + 2 := by
  refine ⟨Q / 3, ?_⟩
  have hmod := Nat.mod_lt Q (by omega : 0 < 3)
  have hdecomp := Nat.mod_add_div Q 3
  omega

theorem tribonacci_inverse_lt_middle : t ^ (-1 : Int) < t - 1 := by
  have hphi : Real.goldenRatio < t := by
    rw [← dbonacciPerronRoot_two_eq_goldenRatio,
      ← dbonacciPerronRoot_three_eq_tribonacciConstant]
    exact dbonacciPerronRoot_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  have hproduct :
      0 < (t - Real.goldenRatio) * (t + Real.goldenRatio - 1) := by
    exact mul_pos (sub_pos.mpr hphi) (by nlinarith [Real.one_lt_goldenRatio])
  have hquad : 1 < t ^ 2 - t := by
    nlinarith [Real.goldenRatio_sq]
  rw [zpow_neg, zpow_one]
  by_contra hnot
  have hle : t - 1 <= t⁻¹ := le_of_not_gt hnot
  have hscaled := mul_le_mul_of_nonneg_left hle tribonacciConstant_pos.le
  rw [mul_inv_cancel₀ tribonacciConstant_ne_zero] at hscaled
  nlinarith

/-- The real-line endpoint has a three-phase survivor orbit with exact liminf
`t^-1`, far above the period-two orbit's low arm. -/
theorem tribonacci_survivor_one_liminf :
    Filter.liminf (fun Q => tribonacciSurvivor Q 1) Filter.atTop =
      t ^ (-1 : Int) := by
  have hinverse_lt_one : t ^ (-1 : Int) < 1 := by
    simpa [zpow_neg] using inv_lt_one_of_one_lt₀ one_lt_tribonacciConstant
  have hlower : ∀ᶠ Q in Filter.atTop,
      t ^ (-1 : Int) <= tribonacciSurvivor Q 1 := by
    filter_upwards [] with Q
    rcases tribonacci_nat_mod_three Q with ⟨k, rfl | rfl | rfl⟩
    · rw [tribonacci_survivor_one_mod_zero]
      exact hinverse_lt_one.le
    · rw [tribonacci_survivor_one_mod_one]
      exact tribonacci_inverse_lt_middle.le
    · rw [tribonacci_survivor_one_mod_two]
  have hupper : ∀ᶠ Q in Filter.atTop,
      tribonacciSurvivor Q 1 <= (1 : Real) := by
    filter_upwards [] with Q
    rcases tribonacci_nat_mod_three Q with ⟨k, rfl | rfl | rfl⟩
    · rw [tribonacci_survivor_one_mod_zero]
    · rw [tribonacci_survivor_one_mod_one]
      nlinarith [tribonacciConstant_lt_two]
    · rw [tribonacci_survivor_one_mod_two]
      exact hinverse_lt_one.le
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨3 * N + 2, by omega, ?_⟩
      rw [tribonacci_survivor_one_mod_two]
    · exact ⟨t ^ (-1 : Int), hlower⟩
  · exact Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop hupper) hlower

theorem tribonacci_low_arm_lt_terminal_liminf :
    (1 - t ^ (-1 : Int)) / 2 < t ^ (-1 : Int) := by
  have hhalf : (2 : Real)⁻¹ < t⁻¹ :=
    (inv_lt_inv₀ (by norm_num : (0 : Real) < 2) tribonacciConstant_pos).2
      tribonacciConstant_lt_two
  norm_num at hhalf
  norm_num only [zpow_neg, zpow_one]
  nlinarith

/-- Therefore the requested unrestricted upper bound is false even at the
natural endpoint `x = 1`; no finite forbidden-region depth can prove it. -/
theorem tribonacci_unrestricted_global_liminf_upper_bound_false :
    ¬∀ x : Real,
      Filter.liminf (fun Q => tribonacciSurvivor Q x) Filter.atTop <=
        championValue t := by
  intro hglobal
  have hone := hglobal 1
  rw [tribonacci_survivor_one_liminf, championValue_tribonacciConstant] at hone
  norm_num only [zpow_neg, zpow_one] at hone
  have hstrict := tribonacci_low_arm_lt_terminal_liminf
  norm_num only [zpow_neg, zpow_one] at hstrict
  exact (not_le_of_gt hstrict) hone

end D5.S0.Tower.DBonacciGeneral.TribonacciGlobalBound
