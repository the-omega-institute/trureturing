/- GID: D5/S3/Analytic/CothBernoulliDegree/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/CothBernoulliDegree/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.PSeries]
   utility: none
   digest: The two derivative sign clauses for the signed hyperbolic cotangent Bernoulli remainder. -/

import Mathlib.Analysis.PSeries
import D5.S3.Analytic.CothBernoulliDegree.Kernel
import D5.S3.Analytic.CothBernoulliDegree.PartialFraction

namespace D5.S3.Analytic.CothBernoulliDegree.Result

open scoped BigOperators
open Defs PartialFraction Kernel

private lemma negative_phase_sum (n M : ℕ) (hn : 2 ≤ n) (hM : 5 ≤ M) :
    (∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ (2*n+1)) *
      ((1 + (5 / ((M : ℝ) * ((k : ℝ) + 1))) ^ 2 : ℝ) ^ (-(M : ℝ) / 2)) *
      Real.sin ((M : ℝ) * Real.arctan (5 / ((M : ℝ) * ((k : ℝ) + 1))))) ≤
      -(1 : ℝ) / 16 := by
  let w : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) ^ (2*n+1)
  let A : ℕ → ℝ := fun k =>
    (1 + (5 / ((M : ℝ) * ((k : ℝ) + 1))) ^ 2 : ℝ) ^ (-(M : ℝ) / 2)
  let F : ℕ → ℝ := fun k => w k * A k *
    Real.sin ((M : ℝ) * Real.arctan (5 / ((M : ℝ) * ((k : ℝ) + 1))))
  have hw : Summable w := by
    have hb : Summable (fun k : ℕ => 1 / (k : ℝ) ^ (2*n+1)) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    simpa only [w, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hb
  have hbound (k : ℕ) : ‖F k‖ ≤ w k := by
    have hw0 : 0 ≤ w k := by dsimp [w]; positivity
    have hA0 : 0 ≤ A k := by dsimp [A]; positivity
    have hA1 : A k ≤ 1 := by
      dsimp [A]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · nlinarith [sq_nonneg (5 / ((M : ℝ) * ((k : ℝ) + 1)))]
      · have : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
        linarith
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hA0]
    calc
      _ ≤ w k * A k * 1 := mul_le_mul_of_nonneg_left
        (Real.abs_sin_le_one _) (mul_nonneg hw0 hA0)
      _ ≤ w k := by nlinarith [mul_le_mul_of_nonneg_left hA1 hw0]
  have hf : Summable F := hw.of_norm_bounded hbound
  have hfirst : F 0 ≤ -(1 : ℝ) / 8 := by
    simpa [F, w, A] using phase_bound (M : ℝ) (by exact_mod_cast hM)
  have htail : (∑' k : ℕ, F (k + 1)) ≤ (1 : ℝ) / 16 := by
    calc
      _ ≤ ∑' k : ℕ, w (k + 1) := by
        apply Summable.tsum_le_tsum _ ((summable_nat_add_iff 1).2 hf)
          ((summable_nat_add_iff 1).2 hw)
        intro k
        exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound (k + 1))
      _ ≤ (1 : ℝ) / 16 := by
        simpa only [w, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
          tail_bound n hn
  change (∑' k : ℕ, F k) ≤ _
  rw [hf.tsum_eq_zero_add]
  linarith


private lemma negative_mixture (M n : ℕ) (hM : 5 ≤ M) (hn : 2 ≤ n) :
    2 * (∑' k : ℕ, (1/(Real.pi*((k:ℝ)+1))^(2*n)) *
      iteratedDeriv (M-1) (fun s : ℝ => s^M/(s^2+(Real.pi*((k:ℝ)+1))^2))
        (5*Real.pi/(M:ℝ))) ≤
      -(M-1).factorial / (8*Real.pi^(2*n+1)) := by
  let c : ℝ := (M-1).factorial / Real.pi^(2*n+1)
  let f : ℕ → ℝ := fun k => (1/((k:ℝ)+1)^(2*n+1)) *
    ((1+(5/((M:ℝ)*((k:ℝ)+1)))^2 :ℝ)^(-(M:ℝ)/2)) *
      Real.sin ((M:ℝ)*Real.arctan (5/((M:ℝ)*((k:ℝ)+1))))
  have he (k : ℕ) : (1/(Real.pi*((k:ℝ)+1))^(2*n)) *
      iteratedDeriv (M-1) (fun s : ℝ => s^M/(s^2+(Real.pi*((k:ℝ)+1))^2))
        (5*Real.pi/(M:ℝ)) = c*f k := by
    have hc := kernel_deriv_succ (M-2) (Real.pi*((k:ℝ)+1))
      (5*Real.pi/(M:ℝ)) (by positivity)
    rw [show M-2+1=M-1 by omega, show M-2+2=M by omega] at hc
    rw [hc]
    have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    have hk0 : (k:ℝ)+1 ≠ 0 := by positivity
    have ht : (5*Real.pi/(M:ℝ))/(Real.pi*((k:ℝ)+1)) =
        5/((M:ℝ)*((k:ℝ)+1)) := by field_simp
    rw [ht]
    dsimp [c, f]
    rw [pow_succ, pow_succ, mul_pow]
    field_simp
    <;> ring
  calc
    _ = 2*c*(∑' k : ℕ, f k) := by
      simp_rw [he]
      rw [tsum_mul_left]
      ring
    _ ≤ 2*c*(-(1:ℝ)/16) := mul_le_mul_of_nonneg_left
      (negative_phase_sum n M hn hM) (by dsimp [c]; positivity)
    _ = _ := by dsimp [c]; field_simp; ring


/-- Both derivative sign clauses for the signed Bernoulli remainder. -/
theorem result : claim := by
  intro m n hm hn
  have hM : 5 ≤ m+2*n := by omega
  constructor
  · intro t ht
    rw [iteratedDeriv_P m n (m+2*n-2) ht]
    apply mul_pos (by norm_num : (0:ℝ) < 2)
    have hs := (hasSum_iteratedDeriv_P m n (m+2*n-2) ht).summable
    have hpos (k : ℕ) : 0 <
        (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
          iteratedDeriv (m+2*n-2) (fun s : ℝ =>
            s ^ (m+2*n) / (s^2+(Real.pi*((k:ℝ)+1))^2)) t := by
      apply mul_pos (by positivity)
      have h := kernel_deriv_N_pos (m+2*n-2) (Real.pi*((k:ℝ)+1)) t
        (by positivity) ht
      simpa only [show m+2*n-2+2=m+2*n by omega] using h
    exact hs.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  · intro hall
    have ht : 0 < 5*Real.pi/((m+2*n:ℕ):ℝ) := by positivity
    have hpos := hall (5*Real.pi/((m+2*n:ℕ):ℝ)) ht
    rw [iteratedDeriv_P m n (m+2*n-1) ht] at hpos
    have hneg := negative_mixture (m+2*n) n hM hn
    have hstrict : -(m+2*n-1).factorial / (8*Real.pi^(2*n+1)) < (0:ℝ) := by
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) (by positivity)
    linarith


end D5.S3.Analytic.CothBernoulliDegree.Result
