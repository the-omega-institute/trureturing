/- GID: D5/S1/Recurrence/Algebraic/SchroderRatioLimit
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/SchroderRatioLimit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Schroder]
   utility: none
   digest: Unconditional fixed-shift ratio limits for the native large Schroder numbers. -/

import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace D5.S1.Recurrence.Algebraic.SchroderRatioLimit

open PowerSeries Filter
open scoped Topology

private theorem schroder_recurrence (n : ℕ) :
    ((n : ℝ) + 3) * (Nat.largeSchroder (n + 2) : ℝ) =
      (6 * (n : ℝ) + 9) * (Nat.largeSchroder (n + 1) : ℝ) -
        (n : ℝ) * (Nat.largeSchroder n : ℝ) := by
  let F : PowerSeries ℝ := largeSchroderSeries.map (Nat.castRingHom ℝ)
  let H : PowerSeries ℝ := X * F
  have hF : F = 1 + X * F + X * F ^ 2 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℝ))
      largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simpa only [map_add, map_one, map_mul, map_X, map_pow, F] using h
  have hH : H = X + X * H + H ^ 2 := by
    dsimp [H]
    linear_combination (X : PowerSeries ℝ) * hF
  have hd := congrArg (derivative ℝ) hH
  simp only [map_add, Derivation.leibniz, derivative_X, derivative_pow,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, smul_eq_mul, mul_one] at hd
  have hy : (1 - X - 2 * H) * derivative ℝ H = 1 + H := by
    linear_combination hd
  have hs : (1 - X - 2 * H) ^ 2 = 1 - 6 * X + X ^ 2 := by
    linear_combination -4 * hH
  have hl : (1 - 6 * X + X ^ 2) * derivative ℝ H =
      1 + X + (X - 3) * H := by
    calc
      _ = (1 - X - 2 * H) * ((1 - X - 2 * H) * derivative ℝ H) := by
        rw [← hs]
        ring
      _ = (1 - X - 2 * H) * (1 + H) := by rw [hy]
      _ = _ := by linear_combination 2 * hH
  have hc : derivative ℝ H - 6 * (X * derivative ℝ H) +
      X * (X * derivative ℝ H) = 1 + X + X * H - 3 * H := by
    linear_combination hl
  have hcoeff (j : ℕ) : coeff (j + 1) H = (Nat.largeSchroder j : ℝ) := by
    simp [H, F, coeff_succ_X_mul, coeff_map]
  have hmul (a : ℕ) (U : PowerSeries ℝ) :
      coeff (n + 2) ((a : PowerSeries ℝ) * U) = (a : ℝ) * coeff (n + 2) U := by
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hn := congrArg (coeff (n + 2)) hc
  simp only [map_add, map_sub] at hn
  have h6 := hmul 6 (X * derivative ℝ H)
  have h3 := hmul 3 H
  norm_num only [Nat.cast_ofNat] at h6 h3
  rw [h6, h3] at hn
  simp only [coeff_succ_X_mul,
    coeff_derivative, coeff_one, coeff_X, show n + 2 ≠ 0 by omega,
    show n + 2 ≠ 1 by omega, if_false, zero_add, hcoeff] at hn
  push_cast at hn
  nlinarith only [hn]

private theorem schroder_positive (n : ℕ) : 0 < Nat.largeSchroder n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.largeSchroder_succ]
    exact lt_of_lt_of_le ih (Nat.le_add_right _ _)

private theorem schroder_le_succ (n : ℕ) :
    Nat.largeSchroder n ≤ Nat.largeSchroder (n + 1) := by
  rw [Nat.largeSchroder_succ]
  exact Nat.le_add_right _ _

private theorem adjacent_control (n : ℕ) :
    0 ≤ (Nat.largeSchroder n : ℝ) / (Nat.largeSchroder (n + 1) : ℝ) -
      (Real.sqrt (2 : ℝ) - 1) ^ 2 ∧
    ((n : ℝ) + 1) *
      ((Nat.largeSchroder n : ℝ) / (Nat.largeSchroder (n + 1) : ℝ) -
        (Real.sqrt (2 : ℝ) - 1) ^ 2) ≤ 1 := by
  let q : ℕ → ℝ := fun j =>
    (Nat.largeSchroder j : ℝ) / (Nat.largeSchroder (j + 1) : ℝ)
  let c : ℝ := (Real.sqrt (2 : ℝ) - 1) ^ 2
  change 0 ≤ q n - c ∧ ((n : ℝ) + 1) * (q n - c) ≤ 1
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt0 := Real.sqrt_nonneg (2 : ℝ)
  have hcform : c = 3 - 2 * Real.sqrt 2 := by dsimp [c]; nlinarith only [hsqrt]
  have hc0 : 0 ≤ c := sq_nonneg _
  have hcquarter : c ≤ 1 / 4 := by rw [hcform]; nlinarith [hsqrt, hsqrt0]
  have hceq : c ^ 2 - 6 * c + 1 = 0 := by rw [hcform]; nlinarith only [hsqrt]
  have hp (j : ℕ) : 0 < (Nat.largeSchroder j : ℝ) := by
    exact_mod_cast schroder_positive j
  have hq (j : ℕ) : 0 ≤ q j ∧ q j ≤ 1 := by
    refine ⟨div_nonneg (hp j).le (hp (j + 1)).le, ?_⟩
    apply (div_le_one (hp (j + 1))).mpr
    exact_mod_cast schroder_le_succ j
  have hr (j : ℕ) :
      q (j + 1) * (6 * (j : ℝ) + 9 - (j : ℝ) * q j) = (j : ℝ) + 3 := by
    have h := schroder_recurrence j
    have hj1 := ne_of_gt (hp (j + 1))
    have hj2 := ne_of_gt (hp (j + 2))
    calc
      _ = ((6 * (j : ℝ) + 9) * (Nat.largeSchroder (j + 1) : ℝ) -
          (j : ℝ) * (Nat.largeSchroder j : ℝ)) /
            (Nat.largeSchroder (j + 2) : ℝ) := by
        dsimp [q]
        rw [show j + 1 + 1 = j + 2 by omega]
        field_simp
      _ = _ := by rw [← h]; exact mul_div_cancel_right₀ _ hj2
  induction n with
  | zero =>
    norm_num [q]
    constructor <;> linarith
  | succ n ih =>
    let D : ℝ := 6 * (n : ℝ) + 9 - (n : ℝ) * q n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hD : 3 * ((n : ℝ) + 2) ≤ D := by
      dsimp [D]
      nlinarith [mul_nonneg hn (sub_nonneg.mpr (hq n).2)]
    have hDpos : 0 < D := by nlinarith
    have he : D * (q (n + 1) - c) =
        3 - 9 * c + (n : ℝ) * c * (q n - c) := by
      dsimp [D]
      linear_combination hr n + (n : ℝ) * hceq
    have hlow : 0 ≤ q (n + 1) - c := by
      apply (mul_nonneg_iff_of_pos_left hDpos).mp
      rw [he]
      nlinarith [mul_nonneg (mul_nonneg hn hc0) ih.1]
    refine ⟨hlow, ?_⟩
    have hsmall : (n : ℝ) * (q n - c) ≤ 1 := by nlinarith only [ih.1, ih.2]
    have hmul := mul_le_mul_of_nonneg_left hsmall hc0
    have hprod : D * (q (n + 1) - c) ≤ 3 := by rw [he]; nlinarith only [hmul, hc0]
    have hcomp := mul_le_mul_of_nonneg_right hD hlow
    push_cast
    nlinarith only [hcomp, hprod]

/-- For every fixed natural shift, including zero, the ratio of the native large
Schroder numbers converges to the indicated exact power. -/
theorem schroder_ratio_limit : ∀ k : ℕ,
    Tendsto (fun m : ℕ => (Nat.largeSchroder m : ℝ) /
      (Nat.largeSchroder (m + k) : ℝ)) atTop
        (nhds ((Real.sqrt (2 : ℝ) - 1) ^ (2 * k))) := by
  let c : ℝ := (Real.sqrt (2 : ℝ) - 1) ^ 2
  let q : ℕ → ℝ := fun n =>
    (Nat.largeSchroder n : ℝ) / (Nat.largeSchroder (n + 1) : ℝ)
  have hadj : Tendsto q atTop (nhds c) := by
    have hu : Tendsto (fun n : ℕ => c + 1 / ((n : ℝ) + 1)) atTop (nhds c) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)))
    refine tendsto_const_nhds.squeeze hu ?_ ?_
    · intro n
      exact sub_nonneg.mp (adjacent_control n).1
    · intro n
      have h := (adjacent_control n).2
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      have hb : q n - c ≤ 1 / ((n : ℝ) + 1) := by
        apply (le_div_iff₀ hpos).mpr
        simpa only [mul_comm] using h
      linarith only [hb]
  have all_shifts : ∀ k : ℕ,
      Tendsto (fun m : ℕ => (Nat.largeSchroder m : ℝ) /
        (Nat.largeSchroder (m + k) : ℝ)) atTop (nhds (c ^ k)) := by
    intro k
    induction k with
    | zero =>
      have hp (n : ℕ) : (Nat.largeSchroder n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (schroder_positive n))
      simp [hp]
    | succ k ih =>
      have shifted := hadj.comp (tendsto_add_atTop_nat k)
      convert ih.mul shifted using 1
      · ext n
        dsimp [q]
        rw [show n + (k + 1) = n + k + 1 by omega]
        have hp : (Nat.largeSchroder (n + k) : ℝ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (schroder_positive (n + k)))
        field_simp
      · rw [pow_succ]
  intro k
  simpa only [c, pow_mul] using all_shifts k

#print axioms schroder_ratio_limit

end D5.S1.Recurrence.Algebraic.SchroderRatioLimit
