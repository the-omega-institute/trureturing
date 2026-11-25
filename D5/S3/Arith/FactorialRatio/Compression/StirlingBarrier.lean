/- GID: D5/S3/Arith/FactorialRatio/Compression/StirlingBarrier
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/StirlingBarrier
   mirror-E: none(waiver:symbolic-entropy-analysis)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.BinaryEntropy, mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Sum]
   utility: none
   digest: A uniform finite Stirling bound reduces each compact factorial term to its binary entropy sum. -/

import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Tactic

/-!
The factorial arguments may vanish. The binary entropy convention includes
both endpoints, and the error bound holds also at the zero parameter and
the zero window. The finite entropy sum retains the integer parameter of
the original family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier

open Finset Real
open scoped Nat
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd

private def xlog (x : ℝ) : ℝ := x * log x

private def mainTerm (n : ℕ) : ℝ := xlog n - n

private theorem xlog_mul (x y : ℝ) :
    xlog (x * y) = y * xlog x + x * xlog y := by
  by_cases hx : x = 0
  · simp [hx, xlog]
  by_cases hy : y = 0
  · simp [hy, xlog]
  simp only [xlog, Real.log_mul hx hy]
  ring

private theorem factorial_remainder (n s : ℕ) (hns : n ≤ s) :
    0 ≤ log (n ! : ℝ) - mainTerm n ∧
      log (n ! : ℝ) - mainTerm n ≤ log ((s : ℝ) + 1) + 1 := by
  have hlo := Real.le_sum_log_nat n
  rw [Real.sum_log_eq_log_factorial] at hlo
  have hnonneg : 0 ≤ log (n ! : ℝ) - mainTerm n := by
    dsimp [mainTerm, xlog]
    linarith only [hlo]
  refine ⟨hnonneg, ?_⟩
  by_cases hn : n = 0
  · simp only [hn, Nat.factorial_zero, Nat.cast_one, Real.log_one, mainTerm,
      xlog, Nat.cast_zero, zero_mul, sub_zero, sub_self]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ (s : ℝ) + 1 by positivity)]
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hhi := Real.sum_log_le (x := (n : ℝ)) hnR
    rw [Nat.floor_natCast, Real.sum_log_eq_log_factorial] at hhi
    have hl : log (n : ℝ) ≤ log ((s : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by exact_mod_cast (show n ≤ s + 1 by omega))
    dsimp [mainTerm, xlog]
    linarith only [hhi, hl]

private theorem log_selberg (r s b : ℕ) :
    log (selbergFactorial r s b : ℝ) =
      ∑ i ∈ range r, (log (((i + 1) * b)! : ℝ) - log (b ! : ℝ) +
        log ((s - i * b)! : ℝ)) := by
  rw [selbergFactorial_eq_paired, Nat.cast_prod,
    Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr
      (mul_ne_zero (quotient_ne_zero i b) (Nat.factorial_ne_zero _)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, Real.log_mul
    (Nat.cast_ne_zero.mpr (quotient_ne_zero i b))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    Nat.cast_div (Nat.factorial_dvd_factorial (b_le_index_mul i b))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    Real.log_div (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]

private theorem finite_stirling_bound (r s b : ℕ) (hb : r * b ≤ s) :
    |log (selbergFactorial r s b : ℝ) -
      ∑ i ∈ range r, (mainTerm ((i + 1) * b) - mainTerm b + mainTerm (s - i * b))| ≤
      2 * (r : ℝ) * (log ((s : ℝ) + 1) + 1) := by
  rw [log_selberg, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ range r, |(log (((i + 1) * b)! : ℝ) - log (b ! : ℝ) +
        log ((s - i * b)! : ℝ)) -
        (mainTerm ((i + 1) * b) - mainTerm b + mainTerm (s - i * b))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range r, 2 * (log ((s : ℝ) + 1) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hc : (i + 1) * b ≤ s :=
        (Nat.mul_le_mul_right b (Finset.mem_range.mp hi)).trans hb
      have hbs : b ≤ s := (b_le_index_mul i b).trans hc
      have ha := factorial_remainder ((i + 1) * b) s hc
      have hb' := factorial_remainder b s hbs
      have hd := factorial_remainder (s - i * b) s (Nat.sub_le _ _)
      have heq : (log (((i + 1) * b)! : ℝ) - log (b ! : ℝ) +
          log ((s - i * b)! : ℝ)) -
          (mainTerm ((i + 1) * b) - mainTerm b + mainTerm (s - i * b)) =
          ((log (((i + 1) * b)! : ℝ) - mainTerm ((i + 1) * b)) -
            (log (b ! : ℝ) - mainTerm b)) +
            (log ((s - i * b)! : ℝ) - mainTerm (s - i * b)) := by ring
      rw [heq]
      have hB : 0 ≤ log ((s : ℝ) + 1) + 1 := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ (s : ℝ) + 1 by positivity)]
      apply abs_le.mpr
      constructor
      · linarith only [ha.1, hb'.2, hd.1, hB]
      · linarith only [ha.2, hb'.1, hd.2]
    _ = _ := by simp; ring

private theorem entropy_cell (a s : ℕ) (has : a ≤ s) (hs : 0 < s) :
    xlog a + xlog (s - a : ℕ) =
      (s : ℝ) * log s - (s : ℝ) * Real.binEntropy ((a : ℝ) / s) := by
  have hsR : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  have ha : (s : ℝ) * ((a : ℝ) / s) = a := by field_simp
  have hd : (s : ℝ) * (1 - (a : ℝ) / s) = s - a := by field_simp; ring
  have h := congrArg₂ (· + ·)
    (xlog_mul (s : ℝ) ((a : ℝ) / s))
    (xlog_mul (s : ℝ) (1 - (a : ℝ) / s))
  rw [ha, hd, ← Nat.cast_sub has] at h
  simp only [Real.binEntropy, Real.log_inv]
  dsimp [xlog] at h ⊢
  nlinarith only [h]

private theorem finite_energy_identity (r s b : ℕ) (hb : r * b ≤ s) :
    (∑ i ∈ range r, (mainTerm ((i + 1) * b) - mainTerm b + mainTerm (s - i * b))) =
      (r : ℝ) * s * (log s - 1) + (r : ℝ) * b * log r -
        (s : ℝ) * ∑ i ∈ range r, Real.binEntropy (((i * b : ℕ) : ℝ) / s) := by
  by_cases hs : s = 0
  · by_cases hr : r = 0
    · simp [hr]
    · have hb0 : b = 0 := by
        have : r * b = 0 := by omega
        exact (Nat.mul_eq_zero.mp this).resolve_left hr
      simp [hs, hb0, mainTerm, xlog]
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  have hshift : (∑ i ∈ range r, xlog (((i + 1) * b : ℕ) : ℝ)) =
      (∑ i ∈ range r, xlog ((i * b : ℕ) : ℝ)) + xlog ((r * b : ℕ) : ℝ) := by
    have h := Finset.sum_range_succ' (fun i => xlog ((i * b : ℕ) : ℝ)) r
    rw [Finset.sum_range_succ] at h
    simpa [xlog] using h.symm
  have hmass : (∑ i ∈ range r,
      (((i + 1) * b : ℕ) : ℝ) - (b : ℝ) + ((s - i * b : ℕ) : ℝ)) = r * s := by
    calc
      _ = ∑ _i ∈ range r, (s : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hib : i * b ≤ s :=
          (Nat.mul_le_mul_right b (Finset.mem_range.mp hi).le).trans hb
        rw [Nat.cast_sub hib]
        push_cast
        ring
      _ = _ := by simp
  have hc : (∑ i ∈ range r,
      (xlog ((i * b : ℕ) : ℝ) + xlog ((s - i * b : ℕ) : ℝ))) =
      (r : ℝ) * s * log s -
        (s : ℝ) * ∑ i ∈ range r, Real.binEntropy (((i * b : ℕ) : ℝ) / s) := by
    calc
      _ = ∑ i ∈ range r, ((s : ℝ) * log s -
          (s : ℝ) * Real.binEntropy (((i * b : ℕ) : ℝ) / s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply entropy_cell _ _ _ hspos
        exact (Nat.mul_le_mul_right b (Finset.mem_range.mp hi).le).trans hb
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
        ring
  have hlin : (∑ i ∈ range r,
      (mainTerm ((i + 1) * b) - mainTerm b + mainTerm (s - i * b))) =
      (∑ i ∈ range r, (xlog (((i + 1) * b : ℕ) : ℝ) - xlog b +
        xlog ((s - i * b : ℕ) : ℝ))) - r * s := by
    rw [← hmass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [mainTerm]
    ring
  rw [hlin, Finset.sum_add_distrib, Finset.sum_sub_distrib, hshift]
  have hconst : (∑ _i ∈ range r, xlog (b : ℝ)) = (r : ℝ) * xlog b := by simp
  rw [hconst]
  rw [Finset.sum_add_distrib] at hc
  have hboundary := xlog_mul (r : ℝ) (b : ℝ)
  rw [← Nat.cast_mul] at hboundary
  dsimp only [xlog] at hc hboundary ⊢
  nlinarith only [hc, hboundary]

/-- Uniform Stirling reduction for every legal parameter of the actual
compact family. All factorial and entropy endpoints are included. The
error is at most `2*r*(log(s+1)+1)`, independently of `b`. -/
theorem compact_stirling_entropy_bound (r s b : ℕ) (hb : r * b ≤ s) :
    |log (selbergFactorial r s b : ℝ) -
      ((r : ℝ) * s * (log s - 1) + (r : ℝ) * b * log r -
        (s : ℝ) * ∑ i ∈ range r, Real.binEntropy (((i * b : ℕ) : ℝ) / s))| ≤
      2 * (r : ℝ) * (log ((s : ℝ) + 1) + 1) := by
  rw [← finite_energy_identity r s b hb]
  exact finite_stirling_bound r s b hb

end D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier
