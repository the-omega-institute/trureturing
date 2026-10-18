/- GID: D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.claim; result=D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.result; claim=D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.claim
   digest: Early coherent amplitudes refute the odd coprime lattice-walk cross-integral bound. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros

/-! The cross-integral estimate of Dhamapurkar and Deng, arXiv:2309.16352, Eq. (15). -/

set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Dynamics.LatticeWalkCrossIntegralRefutation

open Finset Complex
open scoped ComplexConjugate

/-- The off-diagonal, off-antidiagonal sum in Eq. (B8). -/
def walkTerm (n : ℕ) (l : ℤ) (t : ℝ) : ℂ :=
  ∑ j ∈ range n, ∑ k ∈ range n,
    if j ≠ k ∧ j + k ≠ n then
      Complex.exp (-(Complex.I * t * Real.sin (Real.pi * (j + k) / n) *
        Real.sin (Real.pi * ((j : ℝ) - k) / n))) *
      Complex.exp (2 * Real.pi * Complex.I * l * ((j : ℂ) - k) / n)
    else 0

/-- The uniform cross-integral estimate in Eq. (15). -/
def claim : Prop :=
  ∀ n₁ n₂ : ℕ, Odd n₁ → Odd n₂ → Nat.Coprime n₁ n₂ → n₂ < n₁ →
    ∀ l₁ l₂ : ℕ, l₁ < n₁ → l₂ < n₂ → ∀ T : ℝ, 0 ≤ T →
      ‖∫ t in (0 : ℝ)..T, walkTerm n₁ l₁ t * walkTerm n₂ l₂ t‖ ≤
        32 * n₁ * (n₂ * Real.log n₂) ^ 2 + 32 * n₂ * (n₁ * Real.log n₁) ^ 2

private def angle (n j : ℕ) : ℝ := 2 * Real.pi * j / n

private def mode (n j : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((t / 2 * Real.cos (angle n j) : ℝ) : ℂ) * I) *
    Complex.exp (((angle n j : ℝ) : ℂ) * I)

private def amp (n : ℕ) (t : ℝ) : ℂ := ∑ j ∈ range n, mode n j t

private lemma phase_period (x : ℝ) : Complex.exp (((x + 2 * Real.pi : ℝ) : ℂ) * I) =
    Complex.exp ((x : ℂ) * I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  simp [Complex.ofReal_mul, Complex.exp_two_pi_mul_I]

private lemma phase_two_sum (n : ℕ) (hn : 3 ≤ n) :
    ∑ j ∈ range n, Complex.exp (((2 * angle n j : ℝ) : ℂ) * I) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  let z : ℂ := Complex.exp (2 * Real.pi * I * (2 : ℕ) / n)
  have hz : z ≠ 1 := by
    change Complex.exp (2 * Real.pi * I * (2 : ℕ) / n) ≠ 1
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 2) (by omega : 2 < n)
      ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 2) hn0).mp he)
  have hzpow : z ^ n = 1 := by
    rw [← Complex.exp_nat_mul]
    have he : (n : ℂ) * (2 * Real.pi * I * (2 : ℕ) / n) =
        (2 : ℕ) * (2 * Real.pi * I) := by field_simp (disch := assumption)
    rw [he, Complex.exp_nat_mul_two_pi_mul_I]
  have hs := geom_sum_mul z n
  rw [hzpow, sub_self, mul_eq_zero, sub_eq_zero] at hs
  have hs0 := hs.resolve_right hz
  convert hs0 using 1
  apply sum_congr rfl
  intro j _
  simp only [angle.eq_1, z, ← Complex.exp_nat_mul, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat, Nat.cast_ofNat]
  congr 1
  ring

private lemma mode_pair (n j k : ℕ) (t : ℝ) :
    mode n j t * conj (mode n k t) =
      Complex.exp (-(I * t * Real.sin (Real.pi * (j + k) / n) *
        Real.sin (Real.pi * ((j : ℝ) - k) / n))) *
      Complex.exp (2 * Real.pi * I * (1 : ℤ) * ((j : ℂ) - k) / n) := by
  have hc := Real.cos_sub_cos (angle n j) (angle n k)
  have ha : (angle n j + angle n k) / 2 = Real.pi * (j + k) / n := by
    simp only [angle]; ring
  have hb : (angle n j - angle n k) / 2 = Real.pi * ((j : ℝ) - k) / n := by
    simp only [angle]; ring
  rw [ha, hb] at hc
  have he : mode n j t * conj (mode n k t) =
      Complex.exp ((((t / 2 * (Real.cos (angle n j) - Real.cos (angle n k)) +
        (angle n j - angle n k) : ℝ) : ℂ) * I)) := by
    simp only [mode.eq_1, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
      Complex.conj_I, mul_neg]
    simp only [← Complex.exp_add, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
    congr 1
    ring
  rw [he, hc, Complex.ofReal_add, add_mul, Complex.exp_add]
  congr 1
  · simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    congr 1
    ring
  · simp only [angle.eq_1, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Int.cast_one, mul_one]
    congr 1
    ring

private lemma mode_diagonal (n j : ℕ) (t : ℝ) :
    mode n j t * conj (mode n j t) = 1 := by
  rw [mode_pair]
  simp

private lemma mode_antidiagonal (n j : ℕ) (hj : j ≤ n) (t : ℝ) :
    mode n j t * conj (mode n (n - j) t) = Complex.exp (((2 * angle n j : ℝ) : ℂ) * I) := by
  rw [mode_pair]
  have hs : j + (n - j) = n := Nat.add_sub_of_le hj
  have hn : n = 0 ∨ n ≠ 0 := eq_or_ne n 0
  rcases hn with rfl | hn
  · simp [angle.eq_1]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsR : (j : ℝ) + (n - j : ℕ) = n := by exact_mod_cast hs
  rw [show Real.pi * ((j : ℝ) + (n - j : ℕ)) / n = Real.pi by
    rw [hsR]; field_simp (disch := assumption), Real.sin_pi]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
    one_mul, Int.cast_one, mul_one]
  have he : 2 * Real.pi * I * ((j : ℂ) - (n - j : ℕ)) / n =
      (((2 * angle n j - 2 * Real.pi : ℝ) : ℂ) * I) := by
    simp only [angle.eq_1, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Nat.cast_sub hj]
    field_simp (disch := exact_mod_cast hn)
    ring
  rw [he]
  change Complex.exp (((2 * angle n j - 2 * Real.pi : ℝ) : ℂ) * I) = _
  have hp := phase_period (2 * angle n j - 2 * Real.pi)
  simpa only [sub_add_cancel] using hp.symm

private lemma walk_identity (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) (t : ℝ) :
    walkTerm n 1 t = ((Complex.normSq (amp n t) - (n - 1) : ℝ) : ℂ) := by
  have hzero : 0 ∈ range n := mem_range.mpr (by omega)
  have hdis (j k : ℕ) : ¬ (j = k ∧ j + k = n) := by
    rcases hn with ⟨m, hm⟩
    omega
  let g := fun j k => mode n j t * conj (mode n k t)
  have hsplit (j k : ℕ) :
      g j k = (if j ≠ k ∧ j + k ≠ n then g j k else 0) +
        (if j = k then g j k else 0) + (if j + k = n then g j k else 0) := by
    by_cases hd : j = k <;> by_cases ha : j + k = n <;> simp_all
  have hdiag (j : ℕ) (hj : j ∈ range n) :
      (∑ k ∈ range n, if j = k then g j k else 0) = 1 := by
    simp only [sum_ite_eq, hj, ite_true, g, mode_diagonal]
  have hanti (j : ℕ) (hj : j ∈ range n) :
      (∑ k ∈ range n, if j + k = n then g j k else 0) =
        if j = 0 then 0 else Complex.exp (((2 * angle n j : ℝ) : ℂ) * I) := by
    have hjn := mem_range.mp hj
    by_cases hz : j = 0
    · subst j
      simp only [zero_add, ite_true]
      apply sum_eq_zero
      intro k hk
      rw [ite_eq_right (ne_of_lt (mem_range.mp hk))]
    · have hmem : n - j ∈ range n := mem_range.mpr (by omega)
      simp_rw [show ∀ k, j + k = n ↔ n - j = k by omega]
      rw [sum_ite_eq, ite_eq_left hmem, ite_eq_right hz]
      exact mode_antidiagonal n j (by omega) t
  have hs : (∑ j ∈ range n, if j = 0 then 0 else Complex.exp (((2 * angle n j : ℝ) : ℂ) * I)) = -1 := by
    have he : (∑ j ∈ range n, Complex.exp (((2 * angle n j : ℝ) : ℂ) * I)) =
        (∑ j ∈ range n, if j = 0 then 0 else Complex.exp (((2 * angle n j : ℝ) : ℂ) * I)) + 1 := by
      rw [← sum_erase_add _ _ hzero]
      simp only [angle.eq_1, Nat.cast_zero, mul_zero, zero_div, Complex.ofReal_zero,
        zero_mul, Complex.exp_zero]
      congr 1
      rw [← sum_erase_add _ _ hzero]
      simp only [ite_true, add_zero]
      apply sum_congr rfl
      intro j hj
      rw [ite_eq_right (mem_erase.mp hj).1]
    rw [phase_two_sum n hn3] at he
    linear_combination -he
  have hfull : ((Complex.normSq (amp n t) : ℝ) : ℂ) =
      walkTerm n 1 t + (n : ℂ) - 1 := by
    rw [← Complex.mul_conj]
    change (∑ j ∈ range n, mode n j t) * conj (∑ k ∈ range n, mode n k t) = _
    rw [map_sum, sum_mul]
    simp_rw [mul_sum]
    change (∑ j ∈ range n, ∑ k ∈ range n, g j k) = _
    rw [sum_congr rfl (fun j _ => sum_congr rfl (fun k _ => hsplit j k))]
    simp_rw [sum_add_distrib]
    rw [show (∑ j ∈ range n, ∑ k ∈ range n,
        if j ≠ k ∧ j + k ≠ n then g j k else 0) = walkTerm n 1 t by
      unfold walkTerm
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      simp only [g, mode_pair]]
    rw [sum_congr rfl hdiag, sum_congr rfl hanti, hs]
    simp [sub_eq_add_neg]
  push_cast
  linear_combination -hfull

private lemma cos_square_sum (n : ℕ) (hn : 3 ≤ n) :
    ∑ j ∈ range n, Real.cos (angle n j) ^ 2 = n / 2 := by
  have hnR : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hsin : Real.sin (Real.pi * (2 : ℕ) / n) ≠ 0 := by
    change Real.sin (Real.pi * 2 / n) ≠ 0
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hn0).2
    nlinarith [Real.pi_pos]
  have hs := D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros.sum_sin_sq
    (a := n) (m := 2) (by omega) hsin
  have htotal : (∑ j ∈ range n, Real.sin (angle n j) ^ 2) +
      (∑ j ∈ range n, Real.cos (angle n j) ^ 2) = n := by
    rw [← sum_add_distrib]
    simp only [Real.sin_sq_add_cos_sq, sum_const, card_range, nsmul_eq_mul, mul_one]
  have hs' : (∑ j ∈ range n, Real.sin (angle n j) ^ 2) = n / 2 := by
    convert hs using 1
    apply sum_congr rfl
    intro j _
    congr 2
    unfold angle
    ring
  linarith

private lemma cross_sum_zero (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    ∑ j ∈ range n, Real.cos (t / 2 * Real.cos (angle n j)) *
      Real.sin (angle n j) = 0 := by
  let f := fun j => Real.cos (t / 2 * Real.cos (angle n j)) * Real.sin (angle n j)
  let r := fun j => if j = 0 then 0 else n - j
  have hrmem (j : ℕ) (hj : j ∈ range n) : r j ∈ range n := by
    have hjn := mem_range.mp hj
    simp only [r, mem_range]
    split_ifs <;> omega
  have hrinv (j : ℕ) (hj : j ∈ range n) : r (r j) = j := by
    have hjn := mem_range.mp hj
    simp only [r]
    split_ifs <;> omega
  have hflip (j : ℕ) (hj : j ∈ range n) : f (r j) = -f j := by
    have hjn := mem_range.mp hj
    by_cases hz : j = 0
    · subst j
      simp [r, f, angle.eq_1]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have he : angle n (n - j) = 2 * Real.pi - angle n j := by
        simp only [angle.eq_1, Nat.cast_sub (by omega : j ≤ n)]
        field_simp (disch := assumption)
      simp only [r, ite_eq_right hz, f, he, Real.cos_two_pi_sub, Real.sin_two_pi_sub,
        mul_neg]
  have hs : (∑ j ∈ range n, f (r j)) = ∑ j ∈ range n, f j := by
    apply sum_bij (fun j _ => r j) hrmem
    · intro j hj k hk he
      have hh := congrArg r he
      rwa [hrinv j hj, hrinv k hk] at hh
    · intro j hj
      exact ⟨r j, hrmem j hj, hrinv j hj⟩
    · intro j _
      rfl
  rw [sum_congr rfl hflip, sum_neg_distrib] at hs
  change ∑ j ∈ range n, f j = 0
  linarith

private lemma sin_mul_lower (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : |c| ≤ 1) :
    t / 4 * c ^ 2 ≤ Real.sin (t / 2 * c) * c := by
  have hs (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : x / 2 ≤ Real.sin x := by
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have hx3 : x ^ 3 ≤ x / 4 := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx2)]
    nlinarith [Real.sin_ge_sub_cube hx0]
  have hc1 := (abs_le.mp hc).2
  have hc0 := (abs_le.mp hc).1
  by_cases hsign : 0 ≤ c
  · have hu0 : 0 ≤ t / 2 * c := by positivity
    have hu1 : t / 2 * c ≤ 1 / 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right (hs _ hu0 hu1) hsign
    nlinarith
  · have hu0 : 0 ≤ -(t / 2 * c) := by nlinarith
    have hu1 : -(t / 2 * c) ≤ 1 / 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right (hs _ hu0 hu1) (show 0 ≤ -c by linarith)
    rw [Real.sin_neg] at hh
    nlinarith

private lemma amp_im_lower (n : ℕ) (hn : 3 ≤ n) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : n * t / 8 ≤ (amp n t).im := by
  have him : (amp n t).im =
      ∑ j ∈ range n, Real.sin (t / 2 * Real.cos (angle n j)) *
        Real.cos (angle n j) := by
    simp only [amp.eq_1, Complex.im_sum, mode.eq_1, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sum_add_distrib]
    rw [cross_sum_zero n hn t, zero_add]
  rw [him]
  calc
    (n : ℝ) * t / 8 = ∑ j ∈ range n, t / 4 * Real.cos (angle n j) ^ 2 := by
      rw [← mul_sum, cos_square_sum n hn]
      ring
    _ ≤ _ := sum_le_sum fun j _ =>
      sin_mul_lower t (Real.cos (angle n j)) ht0 ht1 (Real.abs_cos_le_one _)

private lemma amp_normSq_upper (n : ℕ) (t : ℝ) :
    Complex.normSq (amp n t) ≤ (n : ℝ) ^ 2 := by
  have hb : ‖amp n t‖ ≤ (n : ℝ) := by
    calc
      ‖amp n t‖ ≤ ∑ j ∈ range n, ‖mode n j t‖ := norm_sum_le _ _
      _ = n := by
        simp only [mode.eq_1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          sum_const, card_range, nsmul_eq_mul]
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

private lemma amp_normSq_lower (n : ℕ) (hn : 3 ≤ n) (t : ℝ)
    (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    (n : ℝ) ^ 2 / 256 ≤ Complex.normSq (amp n t) := by
  have hi := amp_im_lower n hn t (by linarith) ht1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hil : (n : ℝ) / 16 ≤ (amp n t).im := by nlinarith
  have hisq := Complex.im_sq_le_normSq (amp n t)
  nlinarith

private def profile (n : ℕ) (t : ℝ) : ℝ := Complex.normSq (amp n t) - (n - 1)

private lemma continuous_profile (n : ℕ) : Continuous (profile n) := by
  unfold profile
  apply Continuous.sub _ continuous_const
  apply Complex.continuous_normSq.comp
  unfold amp mode
  fun_prop

private lemma profile_product_lower (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m) (t : ℝ) :
    Complex.normSq (amp n t) * Complex.normSq (amp m t) -
      ((n - 1 : ℝ) * (m : ℝ) ^ 2 + (m - 1 : ℝ) * (n : ℝ) ^ 2) ≤
        profile n t * profile m t := by
  have hn0 : (0 : ℝ) ≤ n - 1 := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm0 : (0 : ℝ) ≤ m - 1 := by
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hnm := mul_le_mul_of_nonneg_left (amp_normSq_upper m t) hn0
  have hmn := mul_le_mul_of_nonneg_left (amp_normSq_upper n t) hm0
  have hpos := mul_nonneg hn0 hm0
  unfold profile
  nlinarith only [hnm, hmn, hpos]

private lemma integral_lower (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m) :
    (n : ℝ) ^ 2 * (m : ℝ) ^ 2 / 131072 -
      (n - 1 : ℝ) * (m : ℝ) ^ 2 - (m - 1 : ℝ) * (n : ℝ) ^ 2 ≤
        ∫ t in (0 : ℝ)..1, profile n t * profile m t := by
  let C : ℝ := (n - 1 : ℝ) * (m : ℝ) ^ 2 + (m - 1 : ℝ) * (n : ℝ) ^ 2
  let f := fun t => profile n t * profile m t
  have hf : Continuous f := (continuous_profile n).mul (continuous_profile m)
  have hlow (t : ℝ) : -C ≤ f t := by
    have hp := profile_product_lower n m hn hm t
    have hz := mul_nonneg (Complex.normSq_nonneg (amp n t))
      (Complex.normSq_nonneg (amp m t))
    dsimp [f, C]
    linarith
  have hhigh (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
      (n : ℝ) ^ 2 * (m : ℝ) ^ 2 / 65536 - C ≤ f t := by
    have hp := profile_product_lower n m hn hm t
    have hnlow := amp_normSq_lower n hn t ht.1 ht.2
    have hmlow := amp_normSq_lower m hm t ht.1 ht.2
    have hprod := mul_le_mul hnlow hmlow (by positivity)
      (Complex.normSq_nonneg (amp n t))
    dsimp [f, C]
    nlinarith only [hp, hprod]
  have hfirst := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := 0) (b := 1 / 2)
    (by norm_num) (intervalIntegrable_const (c := -C))
    (hf.intervalIntegrable _ _) (fun t _ => hlow t)
  have hsecond := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := 1 / 2) (b := 1)
    (by norm_num)
    (intervalIntegrable_const (c := (n : ℝ) ^ 2 * (m : ℝ) ^ 2 / 65536 - C))
    (hf.intervalIntegrable _ _) hhigh
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hf.intervalIntegrable 0 (1 / 2)) (hf.intervalIntegrable (1 / 2) 1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hfirst hsecond
  change _ ≤ ∫ t in (0 : ℝ)..1, f t
  dsimp [C] at hfirst hsecond
  linarith only [hfirst, hsecond, hsplit]

private lemma log_bound (x : ℝ) (hx : 0 < x) (hmax : x ≤ 10000000003) :
    Real.log x < 24 := by
  calc
    Real.log x ≤ Real.log ((2 : ℝ) ^ 34) :=
      Real.log_le_log hx (hmax.trans (by norm_num))
    _ = 34 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ < 24 := by linarith only [Real.log_two_lt_d9]

theorem result : ¬ claim := by
  intro h
  have ho1 : Odd 10000000003 := ⟨5000000001, by norm_num⟩
  have ho2 : Odd 10000000001 := ⟨5000000000, by norm_num⟩
  have hc := h 10000000003 10000000001 ho1 ho2 (by norm_num)
    (by norm_num) 1 1 (by norm_num) (by norm_num) 1 (by norm_num)
  have hi := integral_lower 10000000003 10000000001 (by norm_num) (by norm_num)
  have hw (t : ℝ) : walkTerm 10000000003 1 t * walkTerm 10000000001 1 t =
      ((profile 10000000003 t * profile 10000000001 t : ℝ) : ℂ) := by
    rw [walk_identity _ ho1 (by norm_num), walk_identity _ ho2 (by norm_num)]
    exact (Complex.ofReal_mul _ _).symm
  change ‖∫ t in (0 : ℝ)..1, walkTerm 10000000003 1 t * walkTerm 10000000001 1 t‖ ≤ _ at hc
  simp_rw [hw] at hc
  rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs] at hc
  have hl1 := log_bound 10000000003 (by norm_num) (by norm_num)
  have hl2 := log_bound 10000000001 (by norm_num) (by norm_num)
  have hpos1 : 0 ≤ Real.log 10000000003 := Real.log_nonneg (by norm_num)
  have hpos2 : 0 ≤ Real.log 10000000001 := Real.log_nonneg (by norm_num)
  have hsq1 : Real.log 10000000003 ^ 2 ≤ 24 ^ 2 := by nlinarith only [hl1, hpos1]
  have hsq2 : Real.log 10000000001 ^ 2 ≤ 24 ^ 2 := by nlinarith only [hl2, hpos2]
  have habs := le_abs_self (∫ t in (0 : ℝ)..1,
    profile 10000000003 t * profile 10000000001 t)
  have hnum :
      32 * (10000000003 : ℝ) * (10000000001 * 24) ^ 2 +
        32 * 10000000001 * (10000000003 * 24) ^ 2 <
      (10000000003 : ℝ) ^ 2 * 10000000001 ^ 2 / 131072 -
        (10000000003 - 1) * 10000000001 ^ 2 - (10000000001 - 1) * 10000000003 ^ 2 := by
    norm_num
  simp only [Nat.cast_ofNat] at hc hi
  have hupper :
      32 * (10000000003 : ℝ) * (10000000001 * Real.log 10000000001) ^ 2 +
        32 * 10000000001 * (10000000003 * Real.log 10000000003) ^ 2 ≤
      32 * (10000000003 : ℝ) * (10000000001 * 24) ^ 2 +
        32 * 10000000001 * (10000000003 * 24) ^ 2 := by
    nlinarith only [hsq1, hsq2]
  exact (not_lt_of_ge hi) ((habs.trans (hc.trans hupper)).trans_lt hnum)

end D5.S3.Quantum.Dynamics.LatticeWalkCrossIntegralRefutation
