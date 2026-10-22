/- GID: D5/S3/Analytic/CothBernoulliDegree/PartialFraction
   generality: G
   mirror-B: D5/B/S3/Analytic/CothBernoulliDegree/PartialFraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent, mathlib/module/Mathlib.NumberTheory.ZetaValues, mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.Complex.RealDeriv]
   utility: none
   digest: Partial fractions and local differentiation of the signed hyperbolic cotangent remainder. -/

import D5.S3.Analytic.CothBernoulliDegree.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv

open scoped BigOperators Topology
open Filter
namespace D5.S3.Analytic.CothBernoulliDegree.PartialFraction

private lemma coth_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => 2 / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2))
      (Real.cosh t / Real.sinh t / t - t ^ (-2 : ℤ)) := by
  let z : ℂ := (t : ℂ) * Complex.I / Real.pi
  have hz : z ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hi := congrArg Complex.im hn
    simp [z, Complex.div_ofReal_im] at hi
    have : t / Real.pi > 0 := div_pos ht Real.pi_pos
    linarith
  have h := (summable_cotTerm hz).hasSum
  have he := cot_series_rep' hz
  have hs := h.congr_fun (fun k => (cotTerm_identity hz k).symm)
  rw [← he] at hs
  have hc : (Real.pi : ℂ) * Complex.cot (Real.pi * z) - 1 / z =
      ((Real.cosh t / Real.sinh t / t - t ^ (-2 : ℤ) : ℝ) : ℂ) *
        (-((Real.pi : ℂ) * (t : ℂ) * Complex.I)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hsh : (Real.sinh t : ℂ) ≠ 0 := by exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
    have hpiz : (Real.pi : ℂ) * z = (t : ℂ) * Complex.I := by dsimp [z]; field_simp
    rw [hpiz, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    simp only [zpow_neg, zpow_ofNat]
    dsimp [z]
    field_simp
    simp [Complex.I_sq]
    <;> ring
  have hd : -((Real.pi : ℂ) * (t : ℂ) * Complex.I) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast ht.ne')) Complex.I_ne_zero)
  have hf (k : ℕ) :
      2 * z * (1 / ((z + (k + 1)) * (z - (k + 1)))) /
          (-((Real.pi : ℂ) * (t : ℂ) * Complex.I)) =
        ((2 / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2) : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hden : (t : ℂ) ^ 2 + ((Real.pi : ℂ) * ((k : ℂ) + 1)) ^ 2 ≠ 0 := by
      exact_mod_cast (show t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2 ≠ 0 by positivity)
    have hprod : (z + (k + 1)) * (z - (k + 1)) =
        -((t : ℂ) ^ 2 + ((Real.pi : ℂ) * ((k : ℂ) + 1)) ^ 2) / (Real.pi : ℂ) ^ 2 := by
      dsimp [z]
      field_simp
      <;> ring_nf
      <;> simp [Complex.I_sq]
    rw [hprod]
    push_cast
    dsimp [z]
    field_simp
    <;> ring
  have hres := (hs.div_const (-((Real.pi : ℂ) * (t : ℂ) * Complex.I))).congr_fun (fun k => (hf k).symm)
  rw [hc, mul_div_cancel_right₀ _ hd] at hres
  simpa only [Complex.ofReal_re] using Complex.hasSum_re hres

private lemma scaled_zeta_hasSum {r : ℕ} (hr : r ≠ 0) :
    HasSum (fun k : ℕ => 1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * r))
      ((-1 : ℝ) ^ (r + 1) * 2 ^ (2 * r - 1) *
        (bernoulli (2 * r) : ℝ) / (2 * r).factorial) := by
  have h0 := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat hr)
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by omega : 2 * r ≠ 0),
    div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h0
  convert h0.div_const (Real.pi ^ (2 * r)) using 1
  · ext k
    rw [mul_pow]
    ring
  · have hp : Real.pi ^ (2 * r) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    field_simp
    <;> ring



open D5.S3.Analytic.CothBernoulliDegree.Defs

private lemma remainder_hasSum (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ =>
      2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
        ((Real.pi * ((k : ℝ) + 1)) ^ (2 * n) *
          (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2))) (p n t) := by
  induction n with
  | zero => simpa [p] using coth_hasSum ht
  | succ n ih =>
    let c : ℝ := (2 : ℝ) ^ (2 * (n + 1)) * (bernoulli (2 * (n + 1)) : ℝ) /
      (2 * (n + 1)).factorial
    have hcoeff : HasSum (fun k : ℕ =>
        2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
          (Real.pi * ((k : ℝ) + 1)) ^ (2 * (n + 1))) (c * t ^ (2 * n)) := by
      have h := (scaled_zeta_hasSum (r := n + 1) (by omega)).mul_left
        (2 * (-1 : ℝ) ^ n * t ^ (2 * n))
      convert h using 1
      · ext k
        ring
      · dsimp [c]
        have he : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        have hs : (-1 : ℝ) ^ n * (-1) ^ (n + 1 + 1) = 1 := by
          rw [← pow_add, show n + (n + 1 + 1) = 2 * (n + 1) by omega, pow_mul]
          norm_num
        rw [he, pow_succ (2 : ℝ), show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          pow_succ (2 : ℝ)]
        have hf : (2 * (n + 1)).factorial ≠ 0 := Nat.factorial_ne_zero _
        field_simp
        rw [pow_succ (2 : ℝ)]
        linear_combination -(2 * (bernoulli (2 * n + 1 + 1) : ℝ) * 2 ^ (2 * n)) * hs
    have hp : p (n + 1) t = p n t - c * t ^ (2 * n) := by
      have he : (2 * ((n : ℤ) + 1)) - 2 = ((2 * n : ℕ) : ℤ) := by omega
      simp only [p]
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one, he, zpow_natCast]
      dsimp [c]
      ring
    rw [hp]
    apply (ih.sub hcoeff).congr_fun
    intro k
    have ha : Real.pi * ((k : ℝ) + 1) ≠ 0 := by positivity
    have hd : t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2 ≠ 0 := by positivity
    simp only [Nat.succ_eq_add_one, pow_succ (-1 : ℝ),
      show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    field_simp
    <;> ring

/-- The signed remainder is a positive-weighted rational-kernel series. -/
theorem P_eq_tsum (m n : ℕ) {t : ℝ} (ht : 0 < t) :
    P m n t = 2 * ∑' k : ℕ,
      (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
        (t ^ (m + 2 * n) / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) := by
  have h := (remainder_hasSum n ht).mul_left ((-1 : ℝ) ^ n * t ^ m / 2)
  have hsum : HasSum (fun k : ℕ =>
      (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
        (t ^ (m + 2 * n) / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)))
      (P m n t / 2) := by
    convert h using 1
    · ext k
      have hs : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rw [pow_add]
      field_simp
      nlinarith [hs]
    · dsimp [P]
      ring
  have he := hsum.tsum_eq
  linarith

end D5.S3.Analytic.CothBernoulliDegree.PartialFraction
