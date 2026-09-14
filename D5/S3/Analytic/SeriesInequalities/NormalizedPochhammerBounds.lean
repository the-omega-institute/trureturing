/- GID: D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized complex Pochhammer products satisfy an explicit disk bound. -/
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators
open Finset

namespace D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds

noncomputable def normalizedPochhammer (k : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^k * (descPochhammer ℂ k).eval (z - 1) / (k.factorial : ℂ)

theorem normalized_pochhammer_eq_prod (k : ℕ) (z : ℂ) :
    normalizedPochhammer k z = ∏ j ∈ Finset.range k, (1 - z / ((j + 1 : ℕ) : ℂ)) := by
  unfold normalizedPochhammer
  rw [descPochhammer_eval_eq_prod_range, Nat.factorial_eq_prod_range_add_one]
  push_cast
  rw [show (-1 : ℂ)^k = ∏ _j ∈ range k, (-1 : ℂ) by simp,
    ← prod_mul_distrib, ← prod_div_distrib]
  apply prod_congr rfl
  intro j _
  have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
  field_simp
  ring

theorem normalized_pochhammer_zero (z : ℂ) : normalizedPochhammer 0 z = 1 := by
  simp [normalized_pochhammer_eq_prod]

private theorem factor_sq (z : ℂ) (t : ℝ) (ht : t ≠ 0) :
    ‖1 - z / (t : ℂ)‖ ^ 2 = 1 - 2 * z.re / t + ‖z‖ ^ 2 / t ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.div_ofReal_re, Complex.sub_im, Complex.one_im, Complex.div_ofReal_im]
  field_simp
  ring

private theorem accumulated_product (k : ℕ) (z : ℂ) :
    ‖normalizedPochhammer k z‖ ^ 2 ≤
      Real.exp (-2 * z.re * (harmonic k : ℝ) + ‖z‖ ^ 2 *
        ∑ j ∈ range k, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  rw [normalized_pochhammer_eq_prod, norm_prod, ← prod_pow]
  have hfactor (j : ℕ) :
      ‖1 - z / ((j + 1 : ℕ) : ℂ)‖ ^ 2 ≤
      Real.exp (-2 * z.re / ((j + 1 : ℕ) : ℝ) +
        ‖z‖ ^ 2 / ((j + 1 : ℕ) : ℝ) ^ 2) := by
    have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show ((j + 1 : ℕ) : ℂ) = (((j + 1 : ℕ) : ℝ) : ℂ) by simp,
      factor_sq z _ hj]
    convert Real.add_one_le_exp
      (-2 * z.re / ((j + 1 : ℕ) : ℝ) + ‖z‖ ^ 2 / ((j + 1 : ℕ) : ℝ) ^ 2) using 1
    ring
  calc
    _ ≤ ∏ j ∈ range k, Real.exp (-2 * z.re / ((j + 1 : ℕ) : ℝ) +
        ‖z‖ ^ 2 / ((j + 1 : ℕ) : ℝ) ^ 2) :=
      prod_le_prod (fun _ _ => sq_nonneg _) (fun j _ => hfactor j)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp [harmonic, Rat.cast_sum, Rat.cast_inv, div_eq_mul_inv,
        sum_add_distrib, mul_sum]

private theorem inverse_square_sum (k : ℕ) :
    (∑ j ∈ range k, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have heq : (∑ j ∈ range k, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) =
      ∑ i ∈ Ioo 0 (k + 1), ((i : ℝ) ^ 2)⁻¹ := by
    apply sum_bij (fun j _ => j + 1)
    · intro j hj
      simp only [mem_range] at hj
      simp only [mem_Ioo]
      omega
    · intro a _ b _ hab
      omega
    · intro b hb
      simp only [mem_Ioo] at hb
      exact ⟨b - 1, by simp only [mem_range]; omega, by omega⟩
    · intro j _
      rfl
  rw [heq]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (k + 1))

theorem normalized_pochhammer_norm_le (R : ℝ) (hR : 0 ≤ R) (k : ℕ)
    (hk : 1 ≤ k) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖normalizedPochhammer k z‖ ≤ Real.exp (R + R^2) * Real.rpow (k : ℝ) (-z.re) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlo : Real.log (k : ℝ) ≤ (harmonic k : ℝ) := by
    exact (Real.log_le_log hkpos (by exact_mod_cast Nat.le_succ k)).trans
      (log_add_one_le_harmonic k)
  have hhi := harmonic_le_one_add_log k
  have hre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hz
  have herror : -2 * z.re * ((harmonic k : ℝ) - Real.log k) ≤ 2 * R := by
    have hneg : -z.re ≤ R := by linarith [(abs_le.mp hre).1]
    have hmul := mul_le_mul hneg
      (show (harmonic k : ℝ) - Real.log k ≤ 1 by linarith)
      (by linarith : 0 ≤ (harmonic k : ℝ) - Real.log k) hR
    nlinarith
  have hs := inverse_square_sum k
  have hnorm : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hacc := accumulated_product k z
  have hexp : -2 * z.re * (harmonic k : ℝ) + ‖z‖ ^ 2 *
      (∑ j ∈ range k, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤
      2 * (R + R ^ 2 - z.re * Real.log k) := by
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖z‖)
    nlinarith
  have hsq : ‖normalizedPochhammer k z‖ ^ 2 ≤
      (Real.exp (R + R ^ 2) * Real.rpow (k : ℝ) (-z.re)) ^ 2 := by
    calc
      _ ≤ Real.exp (2 * (R + R ^ 2 - z.re * Real.log k)) :=
        hacc.trans (Real.exp_le_exp.mpr hexp)
      _ = _ := by
        change Real.exp (2 * (R + R ^ 2 - z.re * Real.log k)) =
          (Real.exp (R + R ^ 2) * (k : ℝ) ^ (-z.re)) ^ 2
        rw [Real.rpow_def_of_pos hkpos, ← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
  apply (sq_le_sq₀ (norm_nonneg _) ?_).mp hsq
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
