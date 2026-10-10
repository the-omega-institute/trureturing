/- GID: D5/S3/Arith/LogConvolutionMassExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/LogConvolutionMassExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: Absolute coefficient mass controls a signed logarithmic convolution at every real cutoff. -/

import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.LogConvolutionMassExpansion

open Nat hiding log log_pos
open Real Finset intervalIntegral MeasureTheory
open scoped BigOperators

/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE:
https://github.com/leanprover-community/mathlib4/blob/0826a5e4ff8877949060d03ce8955545bfb2b47f/LICENSE
Authors of the three scalar supplier proofs: Terence Tao.

The next three scalar suppliers are minimal Apache-2.0 ports of
Terence Tao's Mathlib/Analysis/SpecialFunctions/Log/Sum.lean at immutable
commit 0826a5e4ff8877949060d03ce8955545bfb2b47f (copyright 2026 Terence Tao).
Source: https://github.com/leanprover-community/mathlib4/blob/0826a5e4ff8877949060d03ce8955545bfb2b47f/Mathlib/Analysis/SpecialFunctions/Log/Sum.lean
That file is absent from the pinned mathlib. They are used by the live
factorial error estimate below; their proof shape is bind-only port.
Only names, imports, and the Nat.cast_one adaptation are changed. The
convolution/moment/tsum composition below is not a theorem in that source.
Replace them by upstream imports when the pinned library supplies them. -/

theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Real.log n = Real.log (N.factorial : ℝ) := by
  rw [← prod_Ico_id_eq_factorial, ← Real.log_prod (by intros; simp; grind), prod_natCast]
  rfl

private theorem sum_log_floor_upper {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n ≤ x * Real.log x - x + Real.log x + 1 := by
  have aux1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have aux2 : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ ≤ (∫ t in (1 : ℕ)..⌊x⌋₊, Real.log t) + Real.log x := by
      rw [← Icc_add_one_left_eq_Ioc, ← sum_Ico_add_eq_sum_Icc (by simpa)]
      gcongr
      exact (strictMonoOn_log.monotoneOn.mono (by grind)).sum_le_integral_Ico aux2
    _ ≤ (∫ t in 1..x, Real.log t) + Real.log x := by
      grw [Nat.cast_one, integral_mono_interval le_rfl (mod_cast aux2) aux1 _ (by simp)]
      exact ae_restrict_of_forall_mem measurableSet_Ioc fun _ hy ↦ (log_nonneg hy.1.le)
    _ = _ := by grind [integral_log, log_one]

theorem sum_log_floor_lower {x : ℝ} (hx : 1 ≤ x) :
    x * Real.log x - x - Real.log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n := by
  have : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ ≤ (∫ t in 1..x, Real.log t) - ∫ t in ⌊x⌋₊..x, Real.log x := by
      have : x - ⌊x⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one x]
      grw [integral_log, log_one, intervalIntegral.integral_const, smul_eq_mul]
      nlinarith [log_nonneg hx]
    _ ≤ (∫ t in 1..x, Real.log t) - ∫ t in ⌊x⌋₊..x, Real.log t := by
      rify at this
      gcongr
      apply integral_mono_on (Nat.floor_le (by linarith)) (by simp) (by simp)
      grind [log_le_log_iff]
    _ = ∫ t in 1..⌊x⌋₊, Real.log t := by
      rw [integral_symm _ ⌊x⌋₊, sub_neg_eq_add, integral_add_adjacent_intervals] <;> simp
    _ ≤ _ := by
      rw [← Icc_add_one_left_eq_Ioc, zero_add, ← add_sum_Ioc_eq_sum_Icc this, Nat.cast_one,
        log_one, ← Ico_add_one_add_one_eq_Ioc, zero_add, ← sum_Ico_add']
      exact_mod_cast ((strictMonoOn_log.mono (by grind)).monotoneOn.integral_le_sum_Ico this)

/-- The floor factorial error is uniformly bounded on a nonnegative interval.
The value at zero and the subunit interval are included. -/
theorem floor_factorial_log_error (x y : ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    |Real.log (⌊x⌋₊.factorial : ℝ) - (x * Real.log x - x)| ≤ 1 + Real.log y := by
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  by_cases hx1 : 1 ≤ x
  · have hu := sum_log_floor_upper hx1
    have hl := sum_log_floor_lower hx1
    rw [sum_log_eq_log_factorial] at hu hl
    have hlogxy : Real.log x ≤ Real.log y :=
      Real.log_le_log (zero_lt_one.trans_le hx1) hxy
    rw [abs_le]
    constructor <;> linarith
  · have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hx1)
    by_cases hx0 : x = 0
    · simp only [hx0, Nat.floor_zero, Nat.factorial_zero, Nat.cast_one,
        Real.log_one, zero_mul, sub_zero, abs_zero]
      linarith
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx (le_of_not_ge hx1)
    have hF : x * Real.log x - x ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hx hlogx
      linarith
    have hsmall := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hxpos) hx
    rw [mul_sub, mul_one, mul_inv_cancel₀ hx0] at hsmall
    simp only [hfloor, Nat.factorial_zero, Nat.cast_one, Real.log_one, zero_sub,
      abs_neg, abs_of_nonpos hF]
    linarith

/-- An absolutely summable real arithmetic coefficient sequence gives two
absolute weighted moments and a two-term expansion of its logarithmic
Dirichlet convolution at every real cutoff at least one. The error constant
is the entire absolute coefficient mass, with no sign restriction. -/
theorem logarithmic_convolution_mass_expansion
    (g : ArithmeticFunction ℝ) (hg : Summable (fun n : ℕ => |g n|)) :
    Summable (fun n : ℕ => |g n / (n : ℝ)|) ∧
    Summable (fun n : ℕ => |g n * Real.log n / (n : ℝ)|) ∧
    ∀ y : ℝ, 1 ≤ y →
      |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (g * ArithmeticFunction.log) n)
        - (∑' n : ℕ, g n / (n : ℝ)) * y * Real.log y
        + ((∑' n : ℕ, g n / (n : ℝ)) +
            (∑' n : ℕ, g n * Real.log n / (n : ℝ))) * y|
        ≤ (∑' n : ℕ, |g n|) * (1 + Real.log y) := by
  classical
  have hw1 (n : ℕ) : |g n / (n : ℝ)| ≤ |g n| := by
    by_cases hn0 : n = 0
    · simp [hn0]
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hnpos : (0 : ℝ) < n := by linarith
    rw [abs_div, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    apply (div_le_iff₀ hnpos).mpr
    nlinarith [abs_nonneg (g n)]
  have hw2 (n : ℕ) : |g n * Real.log n / (n : ℝ)| ≤ |g n| := by
    by_cases hn0 : n = 0
    · simp [hn0]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlog : Real.log n ≤ (n : ℝ) := (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
    rw [abs_div, abs_mul,
      show |Real.log (n : ℝ)| = Real.log (n : ℝ) from
        abs_of_nonneg (Real.log_natCast_nonneg n),
      show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    apply (div_le_iff₀ hnpos).mpr
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
  have hGabs : Summable (fun n : ℕ => |g n / (n : ℝ)|) :=
    hg.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs, abs_abs] using hw1 n)
  have hCabs : Summable (fun n : ℕ => |g n * Real.log n / (n : ℝ)|) :=
    hg.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs, abs_abs] using hw2 n)
  have hG : Summable (fun n : ℕ => g n / (n : ℝ)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hGabs
  have hC : Summable (fun n : ℕ => g n * Real.log n / (n : ℝ)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hCabs
  refine ⟨hGabs, hCabs, ?_⟩
  intro y hy
  have hypos : 0 < y := zero_lt_one.trans_le hy
  let F : ℝ → ℝ := fun x => x * Real.log x - x
  let e : ℕ → ℝ := fun n => g n * (Real.log (⌊y / (n : ℝ)⌋₊.factorial : ℝ) - F (y / n))
  have hFpoint (n : ℕ) : g n * F (y / n) =
      (y * Real.log y - y) * (g n / (n : ℝ)) - y * (g n * Real.log n / (n : ℝ)) := by
    by_cases hn0 : n = 0
    · simp [hn0, F]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    dsimp [F]
    rw [Real.log_div hypos.ne' hnpos.ne']
    ring
  have hFsum : Summable (fun n : ℕ => g n * F (y / n)) := by
    simp_rw [hFpoint]
    exact (hG.mul_left (y * Real.log y - y)).sub (hC.mul_left y)
  have hFvalue : (∑' n : ℕ, g n * F (y / n)) =
      (∑' n : ℕ, g n / (n : ℝ)) * y * Real.log y -
        ((∑' n : ℕ, g n / (n : ℝ)) +
          (∑' n : ℕ, g n * Real.log n / (n : ℝ))) * y := by
    simp_rw [hFpoint]
    rw [(hG.mul_left _).tsum_sub (hC.mul_left _), hG.tsum_mul_left, hC.tsum_mul_left]
    ring
  have hepoint (n : ℕ) : ‖e n‖ ≤ |g n| * (1 + Real.log y) := by
    by_cases hn0 : n = 0
    · simp [e, hn0]
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hnpos : (0 : ℝ) < n := by linarith
    have hxy : y / (n : ℝ) ≤ y := (div_le_iff₀ hnpos).mpr (by nlinarith)
    have hscalar := floor_factorial_log_error (y / n) y
      (div_nonneg hypos.le (Nat.cast_nonneg n)) hxy hy
    simpa only [e, F, Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_left hscalar (abs_nonneg (g n))
  have hesum : Summable e := (hg.mul_right (1 + Real.log y)).of_norm_bounded hepoint
  have hebound : |∑' n : ℕ, e n| ≤ (∑' n : ℕ, |g n|) * (1 + Real.log y) := by
    have h := tsum_of_norm_bounded (hg.mul_right (1 + Real.log y)).hasSum hepoint
    simpa only [Real.norm_eq_abs, hg.tsum_mul_right] using h
  have hK : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (g * ArithmeticFunction.log) n) =
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, g n * Real.log (⌊y / (n : ℝ)⌋₊.factorial : ℝ) := by
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    simp_rw [ArithmeticFunction.log_apply, sum_log_eq_log_factorial, ← Nat.floor_div_natCast]
  have hfinite : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, g n * Real.log (⌊y / (n : ℝ)⌋₊.factorial : ℝ)) =
      ∑' n : ℕ, g n * Real.log (⌊y / (n : ℝ)⌋₊.factorial : ℝ) := by
    symm
    apply tsum_eq_sum
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hncut : ¬n ≤ ⌊y⌋₊ := by
      intro h
      exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, h⟩)
    have hyn : y < (n : ℝ) := by
      by_contra h
      exact hncut ((Nat.le_floor_iff hypos.le).mpr (le_of_not_gt h))
    have hsmall : y / (n : ℝ) < 1 := (div_lt_iff₀ hnpos).mpr (by simpa using hyn)
    simp [Nat.floor_eq_zero.mpr hsmall]
  have hdecomp : (∑' n : ℕ, g n * Real.log (⌊y / (n : ℝ)⌋₊.factorial : ℝ)) =
      (∑' n : ℕ, g n * F (y / n)) + ∑' n : ℕ, e n := by
    calc
      _ = ∑' n : ℕ, (g n * F (y / n) + e n) := by
        apply tsum_congr
        intro n
        dsimp [e]
        ring
      _ = _ := hFsum.tsum_add hesum
  calc
    _ = |∑' n : ℕ, e n| := by
      rw [hK, hfinite, hdecomp, hFvalue]
      congr 1
      ring
    _ ≤ _ := hebound

end D5.S3.Arith.LogConvolutionMassExpansion
