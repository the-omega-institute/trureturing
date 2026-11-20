/- GID: D5/S3/Analytic/Asymptotics/DirichletPolynomialMeanSquare
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/DirichletPolynomialMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An elementary weighted mean-square bound for a finite Dirichlet polynomial. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! Source draft for the finite Dirichlet-polynomial estimate. -/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace D5.S3.Weil.DirichletPolynomialMeanSquare

private def phase (v t : ℝ) : ℂ := Complex.exp ((v : ℂ) * Complex.I * (t : ℂ))

private def phaseIntegral (A B v : ℝ) : ℂ :=
  ∫ t in A..B, phase v t

private def frequency (m n : ℕ) : ℝ := Real.log (n : ℝ) - Real.log (m : ℝ)

def polynomial (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * phase (-Real.log (n : ℝ)) t

private theorem continuous_phase (v : ℝ) : Continuous (phase v) := by
  unfold phase
  fun_prop

private theorem norm_phase (v t : ℝ) : ‖phase v t‖ = 1 := by
  simp [phase, Complex.norm_exp]

private theorem phase_mul_conj (x y t : ℝ) :
    phase x t * star (phase y t) = phase (x - y) t := by
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem phaseIntegral_zero (A B : ℝ) :
    phaseIntegral A B 0 = ((B - A : ℝ) : ℂ) := by
  simp [phaseIntegral, phase, intervalIntegral.integral_const, Complex.real_smul]

private theorem phaseIntegral_eq {A B v : ℝ} (hv : v ≠ 0) :
    phaseIntegral A B v = (phase v B - phase v A) / ((v : ℂ) * Complex.I) := by
  exact integral_exp_mul_complex
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hv) Complex.I_ne_zero)

private theorem norm_phaseIntegral_le (A B : ℝ) {v : ℝ} (hv : v ≠ 0) :
    ‖phaseIntegral A B v‖ ≤ 2 / |v| := by
  rw [phaseIntegral_eq hv, norm_div, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg v)
  simpa only [norm_phase, one_add_one_eq_two] using norm_sub_le (phase v B) (phase v A)

private def crossTerm (a : ℕ → ℂ) (m n : ℕ) (t : ℝ) : ℂ :=
  a m * star (a n) * phase (frequency m n) t

private theorem continuous_crossTerm (a : ℕ → ℂ) (m n : ℕ) :
    Continuous (crossTerm a m n) :=
  continuous_const.mul (continuous_phase _)

private theorem polynomial_mul_conj (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    polynomial N a t * star (polynomial N a t) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, crossTerm a m n t := by
  unfold polynomial
  change (∑ m ∈ Finset.Icc 1 N, a m * phase (-Real.log (m : ℝ)) t) *
      (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 N, a n * phase (-Real.log (n : ℝ)) t) = _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [map_mul, crossTerm, starRingEnd_apply]
  calc
    _ = a m * star (a n) *
        (phase (-Real.log (m : ℝ)) t * star (phase (-Real.log (n : ℝ)) t)) := by ring
    _ = _ := by rw [phase_mul_conj, show -Real.log (m : ℝ) - -Real.log (n : ℝ) =
      frequency m n by unfold frequency; ring]

private def integratedTerm (A B : ℝ) (a : ℕ → ℂ) (m n : ℕ) : ℂ :=
  a m * star (a n) * phaseIntegral A B (frequency m n)

private theorem integral_norm_sq (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    (∫ t in A..B, ‖polynomial N a t‖ ^ 2) =
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, integratedTerm A B a m n).re := by
  let S := Finset.Icc 1 N
  have hrow (m : ℕ) : Continuous (fun t => ∑ n ∈ S, crossTerm a m n t) :=
    continuous_finsetSum S fun n _ => continuous_crossTerm a m n
  have hsum : Continuous (fun t => ∑ m ∈ S, ∑ n ∈ S, crossTerm a m n t) :=
    continuous_finsetSum S (fun m _ => hrow m)
  change _ = (∑ m ∈ S, ∑ n ∈ S, integratedTerm A B a m n).re
  calc
    _ = ∫ t in A..B, (∑ m ∈ S, ∑ n ∈ S, crossTerm a m n t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      change ‖polynomial N a t‖ ^ 2 = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, crossTerm a m n t).re
      rw [← polynomial_mul_conj]
      change _ = (polynomial N a t * (starRingEnd ℂ) (polynomial N a t)).re
      rw [Complex.mul_conj']
      simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    _ = (∫ t in A..B, ∑ m ∈ S, ∑ n ∈ S, crossTerm a m n t).re :=
      Complex.reCLM.intervalIntegral_comp_comm (hsum.intervalIntegrable A B)
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum
        (fun m _ => (hrow m).intervalIntegrable A B)]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      rw [intervalIntegral.integral_finsetSum
        (fun n _ => (continuous_crossTerm a m n).intervalIntegrable A B)]
      apply Finset.sum_congr rfl
      intro n _
      exact intervalIntegral.integral_const_mul _ _

private def offDiagonal (A B : ℝ) (a : ℕ → ℂ) (m n : ℕ) : ℂ :=
  if m = n then 0 else integratedTerm A B a m n

private theorem integratedTerm_diag (A B : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    integratedTerm A B a n n = (((B - A) * ‖a n‖ ^ 2 : ℝ) : ℂ) := by
  unfold integratedTerm frequency
  rw [sub_self, phaseIntegral_zero]
  change a n * (starRingEnd ℂ) (a n) * _ = _
  rw [Complex.mul_conj']
  push_cast
  ring

private theorem integral_norm_sq_sub_diagonal (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    (∫ t in A..B, ‖polynomial N a t‖ ^ 2) -
        (B - A) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) =
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, offDiagonal A B a m n).re := by
  let S := Finset.Icc 1 N
  have hsplit (m n : ℕ) :
      integratedTerm A B a m n =
        (if m = n then integratedTerm A B a m m else 0) + offDiagonal A B a m n := by
    by_cases h : m = n
    · subst n
      simp [offDiagonal]
    · simp [offDiagonal, h]
  rw [integral_norm_sq]
  change (∑ m ∈ S, ∑ n ∈ S, integratedTerm A B a m n).re -
      (B - A) * (∑ n ∈ S, ‖a n‖ ^ 2) = _
  have hsplitSum :
      (∑ m ∈ S, ∑ n ∈ S, integratedTerm A B a m n) =
      (∑ m ∈ S, integratedTerm A B a m m) +
        ∑ m ∈ S, ∑ n ∈ S, offDiagonal A B a m n := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    calc
      _ = ∑ n ∈ S, ((if m = n then integratedTerm A B a m m else 0) +
          offDiagonal A B a m n) := Finset.sum_congr rfl fun n _ => hsplit m n
      _ = _ := by rw [Finset.sum_add_distrib]; simp [hm]
  have hdiagRe : (∑ m ∈ S, integratedTerm A B a m m).re =
      (B - A) * ∑ m ∈ S, ‖a m‖ ^ 2 := by
    change Complex.reCLM (∑ m ∈ S, integratedTerm A B a m m) = _
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [Complex.reCLM_apply, integratedTerm_diag,
      Complex.ofReal_re]
  rw [hsplitSum, Complex.add_re, hdiagRe]
  ring

private def reciprocalGap (m n : ℕ) : ℝ :=
  ((n - m : ℕ) : ℝ)⁻¹ + ((m - n : ℕ) : ℝ)⁻¹

private theorem reciprocalGap_comm (m n : ℕ) : reciprocalGap m n = reciprocalGap n m :=
  add_comm _ _

private def weight (a : ℕ → ℂ) (n : ℕ) : ℝ := (n : ℝ) * ‖a n‖ ^ 2

private def harmonicSum (N : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹

private theorem harmonicSum_le_log (N : ℕ) :
    harmonicSum N ≤ 1 + Real.log (N : ℝ) := by
  simpa only [harmonicSum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log N

private theorem reciprocalGap_row {N m : ℕ} (hm : m ∈ Finset.Icc 1 N) :
    (∑ n ∈ Finset.Icc 1 N, reciprocalGap m n) ≤ 2 * harmonicSum N := by
  let S := Finset.Icc 1 N
  have hmN := (Finset.mem_Icc.mp hm).2
  have hupper : (∑ n ∈ S, ((n - m : ℕ) : ℝ)⁻¹) ≤ harmonicSum N := by
    rw [← Finset.sum_filter_of_ne (p := fun n => m < n) (s := S)
      (f := fun n => ((n - m : ℕ) : ℝ)⁻¹) (by
        intro n _ h
        by_contra! hnm
        exact h (by simp [Nat.sub_eq_zero_of_le hnm]))]
    refine Finset.sum_le_sum_of_injOn (fun n : ℕ => n - m) ?_ ?_ (fun _ _ => le_rfl) ?_
    · intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp (show i ∈ S.filter (m < ·) from hi)).2
      have hj' := (Finset.mem_filter.mp (show j ∈ S.filter (m < ·) from hj)).2
      dsimp only at hij
      omega
    · intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      rcases Finset.mem_filter.mp hn with ⟨hnS, hmn⟩
      have hnN := (Finset.mem_Icc.mp (show n ∈ Finset.Icc 1 N from hnS)).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k _ _
      positivity
  have hlower : (∑ n ∈ S, ((m - n : ℕ) : ℝ)⁻¹) ≤ harmonicSum N := by
    rw [← Finset.sum_filter_of_ne (p := fun n => n < m) (s := S)
      (f := fun n => ((m - n : ℕ) : ℝ)⁻¹) (by
        intro n _ h
        by_contra! hmn
        exact h (by simp [Nat.sub_eq_zero_of_le hmn]))]
    refine Finset.sum_le_sum_of_injOn (fun n : ℕ => m - n) ?_ ?_ (fun _ _ => le_rfl) ?_
    · intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp (show i ∈ S.filter (· < m) from hi)).2
      have hj' := (Finset.mem_filter.mp (show j ∈ S.filter (· < m) from hj)).2
      dsimp only at hij
      omega
    · intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      have hnm := (Finset.mem_filter.mp hn).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k _ _
      positivity
  unfold reciprocalGap
  rw [Finset.sum_add_distrib]
  linarith

private theorem frequency_pos {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    0 < frequency m n := by
  exact sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hm) (by exact_mod_cast hmn))

private theorem ordered_pair_bound (a : ℕ → ℂ) {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    ‖a m‖ * ‖a n‖ * (2 / |frequency m n|) ≤
      2 * ‖a m‖ * ‖a n‖ + (weight a m + weight a n) * reciprocalGap m n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hnR := hmR.trans hmnR
  have hgap := sub_pos.mpr hmnR
  have hf := frequency_pos hm hmn
  have hlog : -frequency m n ≤ (m : ℝ) / n - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hmR hnR)
    rw [Real.log_div hmR.ne' hnR.ne'] at h
    unfold frequency
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlog hnR.le
  have hid : ((m : ℝ) / n - 1) * n = (m : ℝ) - n := by
    field_simp [hnR.ne'] <;> ring
  rw [hid] at hmul
  have hrec : 2 / frequency m n ≤ 2 * (n : ℝ) / ((n : ℝ) - m) :=
    (div_le_div_iff₀ hf hgap).2 (by nlinarith only [hmul])
  have hsq : 2 * (m : ℝ) * ‖a m‖ * ‖a n‖ ≤ weight a m + weight a n := by
    unfold weight
    nlinarith only [mul_nonneg hmR.le (sq_nonneg (‖a m‖ - ‖a n‖)),
      mul_nonneg hgap.le (sq_nonneg ‖a n‖)]
  rw [abs_of_pos hf, reciprocalGap, Nat.sub_eq_zero_of_le hmn.le, Nat.cast_zero,
    inv_zero, add_zero, Nat.cast_sub hmn.le]
  calc
    _ ≤ ‖a m‖ * ‖a n‖ * (2 * (n : ℝ) / ((n : ℝ) - m)) :=
      mul_le_mul_of_nonneg_left hrec (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖a m‖ * ‖a n‖ + (2 * (m : ℝ) * ‖a m‖ * ‖a n‖) / ((n : ℝ) - m) := by
      field_simp [hgap.ne'] <;> ring
    _ ≤ _ := by
      rw [← div_eq_mul_inv]
      exact add_le_add_right (div_le_div_of_nonneg_right hsq hgap.le) _

private theorem norm_offDiagonal_le (A B : ℝ) (a : ℕ → ℂ) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    ‖offDiagonal A B a m n‖ ≤
      2 * ‖a m‖ * ‖a n‖ + (weight a m + weight a n) * reciprocalGap m n := by
  by_cases h : m = n
  · subst n
    simpa [offDiagonal, reciprocalGap] using
      (show 0 ≤ 2 * ‖a m‖ * ‖a m‖ by positivity)
  have hswap : |frequency n m| = |frequency m n| := by
    unfold frequency
    exact abs_sub_comm _ _
  have hf : frequency m n ≠ 0 := by
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact (frequency_pos hm hlt).ne'
    · intro he
      have hh := (abs_pos.mpr (frequency_pos hn hgt).ne')
      rw [hswap, he, abs_zero] at hh
      exact (lt_irrefl _ hh)
  simp only [offDiagonal, if_neg h, integratedTerm, norm_mul, norm_star]
  calc
    _ ≤ ‖a m‖ * ‖a n‖ * (2 / |frequency m n|) :=
      mul_le_mul_of_nonneg_left (norm_phaseIntegral_le A B hf)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := by
      rcases lt_or_gt_of_ne h with hlt | hgt
      · exact ordered_pair_bound a hm hlt
      · simpa only [hswap, reciprocalGap_comm n m, add_comm (weight a n),
          mul_comm ‖a n‖ ‖a m‖, mul_right_comm (2 : ℝ) ‖a n‖ ‖a m‖]
          using ordered_pair_bound a hn hgt

/-- Two-sided error for the finite mean square, with the length-weighted coefficient energy. -/
theorem mean_square_error_le (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    |(∫ t in A..B, ‖polynomial N a t‖ ^ 2) -
        (B - A) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)| ≤
      6 * (∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹) *
        (∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2) := by
  let S := Finset.Icc 1 N
  let W := ∑ n ∈ S, weight a n
  let L := ∑ n ∈ S, ‖a n‖
  let H := harmonicSum N
  have hW (n : ℕ) : 0 ≤ weight a n := by unfold weight; positivity
  have hcs : L ^ 2 ≤ H * W := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (f := fun n => (n : ℝ)⁻¹) (g := weight a) (r := fun n => ‖a n‖)
      (fun _ _ => by positivity) (fun n _ => hW n) ?_
    intro n hn
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)
    unfold weight
    rw [← mul_assoc, inv_mul_cancel₀ hnR, one_mul]
  have hrow : (∑ m ∈ S, ∑ n ∈ S, weight a m * reciprocalGap m n) ≤ (2 * H) * W := by
    calc
      _ = ∑ m ∈ S, weight a m * ∑ n ∈ S, reciprocalGap m n := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ m ∈ S, weight a m * (2 * H) :=
        Finset.sum_le_sum fun m hm =>
          mul_le_mul_of_nonneg_left (reciprocalGap_row hm) (hW m)
      _ = _ := by
        rw [← Finset.sum_mul, mul_comm (2 * H)]
  have hcol : (∑ m ∈ S, ∑ n ∈ S, weight a n * reciprocalGap m n) ≤ (2 * H) * W := by
    rw [Finset.sum_comm]
    refine le_trans (le_of_eq ?_) hrow
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by
      rw [reciprocalGap_comm n m]
  have hprod : (∑ m ∈ S, ∑ n ∈ S, 2 * ‖a m‖ * ‖a n‖) = 2 * L ^ 2 := by
    calc
      _ = ∑ m ∈ S, (2 * ‖a m‖) * L := by simp only [L, Finset.mul_sum]
      _ = (2 * L) * L := by rw [← Finset.sum_mul]; simp only [L, Finset.mul_sum]
      _ = _ := by ring
  rw [integral_norm_sq_sub_diagonal]
  change |(∑ m ∈ S, ∑ n ∈ S, offDiagonal A B a m n).re| ≤ 6 * H * W
  calc
    _ ≤ ‖∑ m ∈ S, ∑ n ∈ S, offDiagonal A B a m n‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, ‖offDiagonal A B a m n‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
        (2 * ‖a m‖ * ‖a n‖ + (weight a m + weight a n) * reciprocalGap m n) := by
      refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => ?_
      exact norm_offDiagonal_le A B a (zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1)
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)
    _ ≤ _ := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      nlinarith only [hprod, hrow, hcol, hcs]

/-- The upper bound on an ordered interval with an absolute logarithmic error constant. -/
theorem mean_square_le (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    (∫ t in A..B, ‖polynomial N a t‖ ^ 2) ≤
      (B - A) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) +
        12 * Real.log (2 * (N : ℝ)) * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2) := by
  by_cases hN : N = 0
  · subst N
    simp [polynomial, Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have he : (1 : ℝ) - 2⁻¹ = 1 / 2 := by norm_num
    rwa [he] at h
  have hH : harmonicSum N ≤ 2 * Real.log (2 * (N : ℝ)) := by
    rw [Real.log_mul (by norm_num) hNp.ne']
    linarith [harmonicSum_le_log N]
  have hW : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have herr := (le_abs_self _).trans (mean_square_error_le N a A B)
  change _ - _ ≤ 6 * harmonicSum N * _ at herr
  have hscale : 6 * harmonicSum N ≤ 12 * Real.log (2 * (N : ℝ)) := by linarith
  nlinarith only [herr, mul_le_mul_of_nonneg_right hscale hW]

private theorem sum_rpow_shift (X N : ℕ) (p : ℝ) :
    (∑ n ∈ Finset.Ico X N, ((n + 1 : ℕ) : ℝ) ^ p) =
      ∑ n ∈ Finset.Ioc X N, (n : ℝ) ^ p := by
  calc
    _ = ∑ n ∈ Finset.Ico (X + 1) (N + 1), (n : ℝ) ^ p :=
      Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ p) X N 1
    _ = _ := by
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega

private theorem rpow_antitoneOn_nat_Icc {X N : ℕ} {p : ℝ} (hX : 1 ≤ X) (hp : p ≤ 0) :
    AntitoneOn (fun t : ℝ => t ^ p) (Set.Icc (X : ℝ) N) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast (zero_lt_one.trans_le hX)
  intro x hx y _ hxy
  exact Real.rpow_le_rpow_of_nonpos (hXr.trans_le hx.1) hxy hp

private theorem sum_tail_rpow_le {X N : ℕ} (hX : 1 ≤ X) {d : ℝ} (hd : 0 < d) :
    (∑ n ∈ Finset.Ioc X N, (n : ℝ) ^ (-1 - d)) ≤ (X : ℝ) ^ (-d) / d := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast (zero_lt_one.trans_le hX)
  rw [← sum_rpow_shift X N]
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi (X : ℝ), t ^ (-1 - d) :=
      (rpow_antitoneOn_nat_Icc (N := N) hX (by linarith)).sum_Ico_le_integral
        (integrableOn_Ioi_rpow_of_lt (by linarith) hXr)
        (fun t ht => Real.rpow_nonneg (hXr.trans ht).le _)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -1 - d < -1) hXr,
        show -1 - d + 1 = -d by ring, div_neg, neg_div, neg_neg]

private theorem sum_rpow_le_of_lt_one {N : ℕ} (hN : 1 ≤ N) {d : ℝ}
    (hd : 0 < d) (hd' : d < 1) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-d)) ≤ (N : ℝ) ^ (1 - d) / (1 - d) := by
  have htail := (rpow_antitoneOn_nat_Icc (N := N) (p := -d) (le_refl 1)
    (neg_nonpos.mpr hd.le)).sum_le_integral_Ico hN
  rw [sum_rpow_shift] at htail
  simp only [Nat.cast_one] at htail
  rw [integral_rpow (Or.inl (by linarith : -1 < -d)), Real.one_rpow,
    show -d + 1 = 1 - d by ring] at htail
  rw [← Finset.sum_erase_add _ _ (Finset.left_mem_Icc.mpr hN), Finset.Icc_erase_left,
    Nat.cast_one, Real.one_rpow]
  apply (add_le_add_left htail 1).trans
  apply (le_div_iff₀ (sub_pos.mpr hd')).mpr
  have hcancel := div_mul_cancel₀ ((N : ℝ) ^ (1 - d) - 1) (sub_ne_zero.mpr hd'.ne')
  nlinarith only [hcancel, hd]

private theorem vertical_cpow_eq {n : ℕ} (hn : 0 < n) (u t : ℝ) :
    (n : ℂ) ^ (-((u : ℂ) + (t : ℂ) * Complex.I)) =
      (((n : ℝ) ^ (-u) : ℝ) : ℂ) * phase (-Real.log (n : ℝ)) t := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.ofReal_cpow hnR, Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero hnC, Complex.cpow_def_of_ne_zero hnC]
  simp only [phase, ← Complex.exp_add, ← Complex.ofReal_natCast, ← Complex.ofReal_log hnR]
  congr 1
  push_cast
  ring

/-- The finite polynomial on a vertical line with vanishing initial coefficients. -/
theorem vertical_mean_square_le {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    {A B u a ε C d : ℝ} (hAB : A ≤ B) (hau : a ≤ u) (hC : 0 ≤ C)
    (hd : 0 < d) (hd' : d < 1) (hd_def : d = 2 * (a - ε) - 1)
    (b : ℕ → ℂ) (hzero : ∀ n ∈ Finset.Icc 1 X, b n = 0)
    (hcoeff : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ C * (n : ℝ) ^ ε) :
    (∫ t in A..B, ‖∑ n ∈ Finset.Icc 1 N,
        b n * (n : ℂ) ^ (-((u : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2) ≤
      C ^ 2 * ((B - A) * ((X : ℝ) ^ (-d) / d) +
        12 * Real.log (2 * (N : ℝ)) * ((N : ℝ) ^ (1 - d) / (1 - d))) := by
  let S := Finset.Icc 1 N
  let coeff (n : ℕ) : ℂ := b n * (((n : ℝ) ^ (-u) : ℝ) : ℂ)
  have hpoint (t : ℝ) :
      (∑ n ∈ S, b n * (n : ℂ) ^ (-((u : ℂ) + (t : ℂ) * Complex.I))) =
        polynomial N coeff t := by
    apply Finset.sum_congr rfl
    intro n hn
    change _ = (b n * (((n : ℝ) ^ (-u) : ℝ) : ℂ)) * phase (-Real.log (n : ℝ)) t
    rw [vertical_cpow_eq (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1), ← mul_assoc]
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖coeff n‖ ^ 2 ≤ C ^ 2 * (n : ℝ) ^ (-1 - d) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnp : (0 : ℝ) < n := zero_lt_one.trans_le hn1
    have hnorm : ‖coeff n‖ ≤ C * (n : ℝ) ^ (ε - u) := by
      dsimp only [coeff]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hnp.le _),
        sub_eq_add_neg, Real.rpow_add hnp, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hcoeff n hn) (Real.rpow_nonneg hnp.le _)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hnp.le _))).2 hnorm
    have he : 2 * (ε - u) ≤ -1 - d := by linarith
    have hpow : ((n : ℝ) ^ (ε - u)) ^ (2 : ℕ) = (n : ℝ) ^ (2 * (ε - u)) := by
      rw [mul_comm (2 : ℝ) (ε - u)]
      simpa using (Real.rpow_mul_natCast hnp.le (ε - u) 2).symm
    rw [mul_pow, hpow] at hsq
    exact hsq.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 he) (sq_nonneg C))
  have hsubset : Finset.Ioc X N ⊆ S := by
    intro n hn
    obtain ⟨hnX, hnN⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨hX.trans hnX.le, hnN⟩
  have hD : (∑ n ∈ S, ‖coeff n‖ ^ 2) ≤ C ^ 2 * ((X : ℝ) ^ (-d) / d) := by
    calc
      _ = ∑ n ∈ Finset.Ioc X N, ‖coeff n‖ ^ 2 := by
        symm
        refine Finset.sum_subset hsubset fun n hn hnot => ?_
        obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
        have hnX : n ≤ X := by
          by_contra! h
          exact hnot (Finset.mem_Ioc.mpr ⟨h, hnN⟩)
        simp [coeff, hzero n (Finset.mem_Icc.mpr ⟨hn1, hnX⟩)]
      _ ≤ ∑ n ∈ Finset.Ioc X N, C ^ 2 * (n : ℝ) ^ (-1 - d) :=
        Finset.sum_le_sum fun n hn => hterm n (hsubset hn)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_tail_rpow_le hX hd) (sq_nonneg C)
  have hW : (∑ n ∈ S, (n : ℝ) * ‖coeff n‖ ^ 2) ≤
      C ^ 2 * ((N : ℝ) ^ (1 - d) / (1 - d)) := by
    calc
      _ ≤ ∑ n ∈ S, (n : ℝ) * (C ^ 2 * (n : ℝ) ^ (-1 - d)) :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hterm n hn) (Nat.cast_nonneg n)
      _ = ∑ n ∈ S, C ^ 2 * (n : ℝ) ^ (-d) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnR : (0 : ℝ) < n := by
          exact_mod_cast (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)
        calc
          _ = C ^ 2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-1 - d)) := by
            rw [Real.rpow_one]
            ring
          _ = _ := by rw [← Real.rpow_add hnR, show 1 + (-1 - d) = -d by ring]
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_rpow_le_of_lt_one hN hd hd') (sq_nonneg C)
  have hlog : 0 ≤ 12 * Real.log (2 * (N : ℝ)) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  change (∫ t in A..B, ‖∑ n ∈ S, b n * (n : ℂ) ^ (-((u : ℂ) +
    (t : ℂ) * Complex.I))‖ ^ 2) ≤ _
  simp_rw [hpoint]
  refine (mean_square_le N coeff A B).trans ?_
  calc
    _ ≤ (B - A) * (C ^ 2 * ((X : ℝ) ^ (-d) / d)) +
        (12 * Real.log (2 * (N : ℝ))) * (C ^ 2 * ((N : ℝ) ^ (1 - d) / (1 - d))) :=
      add_le_add (mul_le_mul_of_nonneg_left hD (sub_nonneg.mpr hAB))
        (mul_le_mul_of_nonneg_left hW hlog)
    _ = _ := by ring

end D5.S3.Weil.DirichletPolynomialMeanSquare
