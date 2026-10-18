/- GID: D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.claim; result=D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.result; claim=D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.claim
   digest: Early coherent amplitudes refute the odd coprime lattice-walk cross-integral bound. -/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The cross-integral estimate of Dhamapurkar and Deng, arXiv:2309.16352, Eq. (15). -/

set_option linter.style.longLine false

public section

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

private def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

private def angle (n j : ℕ) : ℝ := 2 * Real.pi * j / n

private def mode (n j : ℕ) (t : ℝ) : ℂ :=
  phase (t / 2 * Real.cos (angle n j)) * phase (angle n j)

private def amp (n : ℕ) (t : ℝ) : ℂ := ∑ j ∈ range n, mode n j t

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private lemma phase_conj (x : ℝ) : conj (phase x) = phase (-x) := by
  simp [phase, ← Complex.exp_conj]

private lemma phase_period (x : ℝ) : phase (x + 2 * Real.pi) = phase x := by
  rw [phase_add]
  simp [phase, Complex.ofReal_mul, Complex.exp_two_pi_mul_I]

private lemma phase_two_sum (n : ℕ) (hn : 3 ≤ n) :
    ∑ j ∈ range n, phase (2 * angle n j) = 0 := by
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
        (2 : ℕ) * (2 * Real.pi * I) := by field_simp
    rw [he, Complex.exp_nat_mul_two_pi_mul_I]
  have hs := geom_sum_mul z n
  rw [hzpow, sub_self, mul_eq_zero, sub_eq_zero] at hs
  have hs0 := hs.resolve_right hz
  convert hs0 using 1
  apply sum_congr rfl
  intro j _
  simp only [phase, angle, z, ← Complex.exp_nat_mul, Complex.ofReal_mul,
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
  simp only [mode, phase_conj, ← phase_add]
  rw [show t / 2 * Real.cos (angle n j) + angle n j +
      -(t / 2 * Real.cos (angle n k) + angle n k) =
      t / 2 * (Real.cos (angle n j) - Real.cos (angle n k)) +
        (angle n j - angle n k) by ring, hc, phase_add]
  congr 1
  · simp only [phase, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    congr 1
    ring
  · simp only [phase, angle, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Int.cast_one, mul_one]
    congr 1
    ring

private lemma mode_diagonal (n j : ℕ) (t : ℝ) :
    mode n j t * conj (mode n j t) = 1 := by
  rw [mode_pair]
  simp

private lemma mode_antidiagonal (n j : ℕ) (hj : j ≤ n) (t : ℝ) :
    mode n j t * conj (mode n (n - j) t) = phase (2 * angle n j) := by
  rw [mode_pair]
  have hs : j + (n - j) = n := Nat.add_sub_of_le hj
  have hn : n = 0 ∨ n ≠ 0 := eq_or_ne n 0
  rcases hn with rfl | hn
  · simp [phase, angle]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsR : (j : ℝ) + (n - j : ℕ) = n := by exact_mod_cast hs
  rw [show Real.pi * ((j : ℝ) + (n - j : ℕ)) / n = Real.pi by
    rw [hsR]; field_simp, Real.sin_pi]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
    one_mul, Int.cast_one, mul_one]
  have he : 2 * Real.pi * I * ((j : ℂ) - (n - j : ℕ)) / n =
      (((2 * angle n j - 2 * Real.pi : ℝ) : ℂ) * I) := by
    simp only [angle, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Nat.cast_sub hj]
    field_simp
    ring
  rw [he]
  change phase (2 * angle n j - 2 * Real.pi) = _
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
        if j = 0 then 0 else phase (2 * angle n j) := by
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
  have hs : (∑ j ∈ range n, if j = 0 then 0 else phase (2 * angle n j)) = -1 := by
    have he : (∑ j ∈ range n, phase (2 * angle n j)) =
        (∑ j ∈ range n, if j = 0 then 0 else phase (2 * angle n j)) + 1 := by
      rw [← sum_erase_add _ _ hzero]
      simp only [angle, Nat.cast_zero, mul_zero, zero_div, phase, Complex.ofReal_zero,
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
  have hs := congrArg Complex.re (phase_two_sum n hn)
  simp only [Complex.re_sum, phase, Complex.exp_ofReal_mul_I_re, Complex.zero_re,
    Real.cos_two_mul, sum_sub_distrib, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul, mul_one] at hs
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
      simp [r, f, angle]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have he : angle n (n - j) = 2 * Real.pi - angle n j := by
        simp only [angle, Nat.cast_sub (by omega : j ≤ n)]
        field_simp
        ring
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
    have hx3 : x ^ 3 ≤ x / 4 := by nlinarith [mul_nonneg x (1 / 4 - x ^ 2)]
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
    simp only [amp, Complex.im_sum, mode, Complex.mul_im, phase,
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
      _ = n := by simp [mode, phase, norm_mul, Complex.norm_exp_ofReal_mul_I]
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

theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Dynamics.LatticeWalkCrossIntegralRefutation
