/- GID: D5/S3/Analytic/LegendrePrimitiveGap
   generality: G
   mirror-B: D5/B/S3/Analytic/LegendrePrimitiveGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.ShiftedLegendre, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts]
   utility: none
   digest: High shifted Legendre modes have actual primitive energy at most 1/(4q(q+1)) times their complex L2 energy. -/

import D5.S3.Analytic.PolynomialL2Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Complex finite Legendre primitive gap

The actual shifted Legendre coefficients give the weighted Sturm eigenvalue
n(n+1). Inverting the positive high modes and integrating their flux proves
the finite primitive estimate, using the original owner's exact Parseval identity.
-/

noncomputable section

open Polynomial MeasureTheory Set
open scoped Interval ComplexConjugate
open D5.S3.Analytic.PolynomialL2Derivative

namespace D5.S3.Analytic.LegendrePrimitiveGap

private abbrev pv (p : ℂ[X]) (x : ℝ) : ℂ := p.eval (x : ℂ)
private abbrev E (D : ℝ) (f : ℝ → ℂ) : ℝ := ∫ x in Icc 0 D, ‖f x‖ ^ 2
private abbrev primitive (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in 0..x, f t

private lemma energy_eq_intervalIntegral {D : ℝ} (hD : 0 ≤ D)
    (f : ℝ → ℂ) : E D f = ∫ x in 0..D, ‖f x‖ ^ 2 := by
  rw [E, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hD]

private lemma flux_zero (p : ℂ[X]) :
    (-(X * (1 - X) * p.derivative) : ℂ[X]).eval 0 = 0 := by simp

private lemma flux_one (p : ℂ[X]) :
    (-(X * (1 - X) * p.derivative) : ℂ[X]).eval 1 = 0 := by simp

private def flux (p : ℂ[X]) : ℂ[X] := -(X * (1 - X) * p.derivative)
private def sturm (p : ℂ[X]) : ℂ[X] := (flux p).derivative
private def eigenvalue (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 1)

private lemma eigenvalue_pos {n : ℕ} (hn : 1 ≤ n) : 0 < eigenvalue n := by
  unfold eigenvalue
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  positivity

private lemma eigenvalue_mono {q n : ℕ} (hqn : q ≤ n) : eigenvalue q ≤ eigenvalue n := by
  unfold eigenvalue
  have h : (q : ℝ) ≤ n := by exact_mod_cast hqn
  nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]

private lemma coeff_sturm (p : ℂ[X]) (k : ℕ) :
    (sturm p).coeff k =
      (k : ℂ) * ((k : ℂ) + 1) * p.coeff k -
        ((k : ℂ) + 1) ^ 2 * p.coeff (k + 1) := by
  have hf : flux p = X * (X * p.derivative) - X * p.derivative := by
    unfold flux
    ring
  rw [sturm, hf, coeff_derivative, coeff_sub, coeff_X_mul, coeff_X_mul,
    coeff_derivative]
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The coefficient recurrence includes k=n and all k>n. -/
private lemma legendre_coefficient_recurrence (n k : ℕ) :
    ((k : ℂ) + 1) ^ 2 * (legendreC n).coeff (k + 1) =
      ((k : ℂ) * ((k : ℂ) + 1) - (n : ℂ) * ((n : ℂ) + 1)) *
        (legendreC n).coeff k := by
  rw [coeff_legendreC,
    coeff_legendreC]
  by_cases hkn : k ≤ n
  · have h₁ : (n.choose (k + 1) : ℂ) * ((k : ℂ) + 1) =
        (n.choose k : ℂ) * ((n : ℂ) - k) := by
      have h := congrArg (fun m : ℕ => (m : ℂ)) (Nat.choose_succ_right_eq n k)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hkn] using h
    have h₂ : ((n + k).choose n : ℂ) * ((n : ℂ) + k + 1) =
        ((n + (k + 1)).choose n : ℂ) * ((k : ℂ) + 1) := by
      have h := Nat.choose_mul_succ_eq (n + k) n
      have he : n + k + 1 - n = k + 1 := by omega
      rw [he] at h
      exact_mod_cast h
    rw [pow_succ]
    push_cast
    linear_combination
      (-((-1 : ℂ) ^ k) * ((k : ℂ) + 1) * ((n + (k + 1)).choose n : ℂ)) * h₁ +
      (((-1 : ℂ) ^ k) * (n.choose k : ℂ) * ((n : ℂ) - k)) * h₂
  · have hk : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]
    simp

/-- The weighted eigenvalue is proved from the existing actual coefficients. -/
private lemma sturm_legendre (n : ℕ) :
    sturm (legendreC n) =
      C ((eigenvalue n : ℝ) : ℂ) * legendreC n := by
  ext k
  rw [coeff_sturm, coeff_C_mul, legendre_coefficient_recurrence]
  simp only [eigenvalue, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one]
  ring

private lemma sturm_C_mul (a : ℂ) (p : ℂ[X]) :
    sturm (C a * p) = C a * sturm p := by
  have h : flux (C a * p) = C a * flux p := by
    simp only [flux, Polynomial.derivative_C_mul]
    ring
  change (flux (C a * p)).derivative = C a * (flux p).derivative
  rw [h, Polynomial.derivative_C_mul]

private lemma sturm_sum (s : Finset ℕ) (p : ℕ → ℂ[X]) :
    sturm (∑ n ∈ s, p n) = ∑ n ∈ s, sturm (p n) := by
  have h : flux (∑ n ∈ s, p n) = ∑ n ∈ s, flux (p n) := by
    simp only [flux, Polynomial.derivative_sum, Finset.mul_sum]
    exact (Finset.sum_neg_distrib _).symm
  rw [sturm, h, Polynomial.derivative_sum]
  rfl

private def inverseCoefficients (a : ℕ → ℂ) (n : ℕ) : ℂ := a n / (eigenvalue n : ℂ)

private lemma sturm_inverse_expansion (d q : ℕ) (hq : 1 ≤ q) (a : ℕ → ℂ)
    (ha : ∀ n < q, a n = 0) :
    sturm (expansion d (inverseCoefficients a)) =
      expansion d a := by
  unfold expansion
  rw [sturm_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sturm_C_mul, sturm_legendre, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  by_cases hlow : n < q
  · simp [inverseCoefficients, ha n hlow]
  · have hn : 1 ≤ n := by omega
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (eigenvalue_pos hn).ne')

private lemma primitive_sturm (p : ℂ[X]) (x : ℝ) :
    primitive (pv (sturm p)) x = pv (flux p) x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x)
    (fun t _ => ((flux p).hasDerivAt (t : ℂ)).comp_ofReal)
    ((eval_continuous (flux p).derivative).intervalIntegrable 0 x)
  have h0 : (flux p).eval 0 = 0 := flux_zero p
  simpa only [primitive, sturm, pv, Complex.ofReal_zero, h0, sub_zero] using h

/-- Weighted integration by parts, before using any finite expansion. -/
private lemma weighted_energy (p : ℂ[X]) :
    ((∫ x : ℝ in 0..1, (x * (1 - x)) * ‖pv p.derivative x‖ ^ 2 : ℝ) : ℂ) =
      moment (sturm p) (p.map (starRingEnd ℂ)) := by
  rw [sturm, moment_derivative,
    show (flux p).eval 1 = 0 from flux_one p,
    show (flux p).eval 0 = 0 from flux_zero p,
    zero_mul, zero_mul, sub_self, zero_sub]
  rw [Polynomial.derivative_map]
  unfold moment
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [eval_map_conj]
  simp only [pv, flux, eval_neg, eval_mul, eval_X, eval_sub, eval_one,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  have hn : (↑(‖p.derivative.eval (x : ℂ)‖ ^ 2) : ℂ) =
      p.derivative.eval (x : ℂ) * conj (p.derivative.eval (x : ℂ)) := by
    rw [Complex.sq_norm, Complex.mul_conj]
  rw [hn]
  ring

lemma mixed_expansion (d : ℕ) (a b : ℕ → ℂ) :
    moment (expansion d a)
      ((expansion d b).map (starRingEnd ℂ)) =
      ∑ n ∈ Finset.range d, a n * conj (b n) / (2 * (n : ℂ) + 1) := by
  rw [expansion_map_conj]
  change moment (∑ n ∈ Finset.range d, C (a n) * legendreC n)
    (expansion d (fun n => conj (b n))) = _
  rw [moment_sum_left]
  apply Finset.sum_congr rfl
  intro n hn
  rw [moment_C_mul_left,
    moment_expansion_row d n b hn]
  ring

private lemma inverse_weighted_energy (d q : ℕ) (hq : 1 ≤ q) (a : ℕ → ℂ)
    (ha : ∀ n < q, a n = 0) :
    (∫ x : ℝ in 0..1, (x * (1 - x)) *
      ‖pv (expansion d (inverseCoefficients a)).derivative x‖ ^ 2) =
      ∑ n ∈ Finset.range d, ‖a n‖ ^ 2 / weight n / eigenvalue n := by
  apply Complex.ofReal_injective
  rw [weighted_energy, sturm_inverse_expansion d q hq a ha, mixed_expansion]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  simp only [inverseCoefficients, map_div₀, Complex.conj_ofReal,
    weight, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_natCast]
  have he : a n * conj (a n) = (‖a n‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow]
  calc
    _ = (a n * conj (a n)) /
        ((2 * (n : ℂ) + 1) * (eigenvalue n : ℂ)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ = _ := by rw [he]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

private lemma weight_bound {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ 1 / 4 := by
  constructor
  · exact mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  · nlinarith [sq_nonneg (x - 1 / 2)]

private lemma flux_energy_bound (p : ℂ[X]) :
    (∫ x : ℝ in 0..1, ‖pv (flux p) x‖ ^ 2) ≤
      (1 / 4 : ℝ) * (∫ x : ℝ in 0..1, (x * (1 - x)) * ‖pv p.derivative x‖ ^ 2) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (((eval_continuous (flux p)).norm.pow 2).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun x : ℝ =>
      (1 / 4 : ℝ) * ((x * (1 - x)) * ‖pv p.derivative x‖ ^ 2))).intervalIntegrable 0 1)
  intro x hx
  have hw := weight_bound hx
  have he : pv (flux p) x = -(↑(x * (1 - x)) * pv p.derivative x) := by
    simp [flux, pv]
  change ‖pv (flux p) x‖ ^ 2 ≤ _
  rw [he, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1,
    mul_pow]
  have hw2 := mul_le_mul_of_nonneg_right hw.2 hw.1
  have hb := mul_le_mul_of_nonneg_right hw2 (sq_nonneg ‖pv p.derivative x‖)
  simpa only [pow_two, mul_assoc] using hb

private lemma coefficient_gap (d q : ℕ) (hq : 1 ≤ q) (a : ℕ → ℂ)
    (ha : ∀ n < q, a n = 0) :
    (∑ n ∈ Finset.range d, ‖a n‖ ^ 2 / weight n / eigenvalue n) ≤
      (1 / eigenvalue q) * coefficientEnergy d a := by
  unfold coefficientEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hlow : n < q
  · simp [ha n hlow]
  · have hnq : q ≤ n := by omega
    have hnum : 0 ≤ ‖a n‖ ^ 2 / weight n := by
      unfold weight
      positivity
    calc
      ‖a n‖ ^ 2 / weight n / eigenvalue n ≤
          ‖a n‖ ^ 2 / weight n / eigenvalue q :=
        div_le_div_of_nonneg_left hnum (eigenvalue_pos hq) (eigenvalue_mono hnq)
      _ = _ := by ring

/-- Complete finite high-mode argument; all coefficients are complex. -/
theorem complex_legendre_primitive_gap (d q : ℕ) (hq : 1 ≤ q) (a : ℕ → ℂ)
    (ha : ∀ n < q, a n = 0) :
    (∫ x in Icc (0 : ℝ) 1, ‖∫ t in (0 : ℝ)..x, (expansion d a).eval (t : ℂ)‖ ^ 2) ≤
      (1 / (4 * (q : ℝ) * ((q : ℝ) + 1))) *
        (∫ x in Icc (0 : ℝ) 1, ‖(expansion d a).eval (x : ℂ)‖ ^ 2) := by
  change E 1 (primitive (pv (expansion d a))) ≤ _
  let F := expansion d (inverseCoefficients a)
  have hF : sturm F = expansion d a :=
    sturm_inverse_expansion d q hq a ha
  have hp : primitive (pv (expansion d a)) = pv (flux F) := by
    rw [← hF]
    funext x
    exact primitive_sturm F x
  rw [energy_eq_intervalIntegral (by norm_num), hp]
  calc
    (∫ x : ℝ in 0..1, ‖pv (flux F) x‖ ^ 2) ≤
        (1 / 4 : ℝ) * (∫ x : ℝ in 0..1, x * (1 - x) * ‖pv F.derivative x‖ ^ 2) :=
      flux_energy_bound F
    _ = (1 / 4 : ℝ) *
        (∑ n ∈ Finset.range d, ‖a n‖ ^ 2 / weight n / eigenvalue n) := by
      rw [inverse_weighted_energy d q hq a ha]
    _ ≤ (1 / 4 : ℝ) * ((1 / eigenvalue q) * coefficientEnergy d a) := by
      gcongr
      exact coefficient_gap d q hq a ha
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), expansion_parseval]
      simp only [eigenvalue, div_eq_mul_inv, mul_inv_rev]
      ring

end D5.S3.Analytic.LegendrePrimitiveGap
