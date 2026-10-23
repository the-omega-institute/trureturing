/- GID: D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Endpoint-adapted original Bernstein coefficients control Taylor coefficient tails. -/

import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

open Finset Polynomial Complex
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

/-- The original normalized Bernstein polynomial, with complex scalars allowed. -/
def bernsteinRealization (d : ℕ) (c : Fin (d + 1) → ℂ) : ℂ[X] :=
  ∑ i : Fin (d + 1), C (c i) * bernsteinPolynomial ℂ d i

private lemma original_coefficients_bound (d : ℕ) (c : Fin (d + 1) → ℂ)
    {B : ℝ} (hc : ∀ i, ‖c i‖ ≤ B) (z : ℂ) :
    ‖(bernsteinRealization d c).eval z‖ ≤ B * (‖z‖ + ‖1 - z‖) ^ d := by
  have hB : 0 ≤ B := (norm_nonneg (c ⟨0, by omega⟩)).trans (hc _)
  calc
    ‖(bernsteinRealization d c).eval z‖
        = ‖∑ i : Fin (d + 1), c i * (d.choose i : ℂ) * z ^ (i : ℕ) *
            (1 - z) ^ (d - (i : ℕ))‖ := by
          simp [bernsteinRealization, eval_finsetSum, bernsteinPolynomial, mul_assoc]
    _ ≤ ∑ i : Fin (d + 1), ‖c i * (d.choose i : ℂ) * z ^ (i : ℕ) *
            (1 - z) ^ (d - (i : ℕ))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (d + 1), B * (d.choose i : ℝ) * ‖z‖ ^ (i : ℕ) *
            ‖1 - z‖ ^ (d - (i : ℕ)) := by
          apply sum_le_sum
          intro i _
          simp only [norm_mul, norm_pow, Complex.norm_natCast]
          gcongr
          exact hc i
    _ = B * (‖z‖ + ‖1 - z‖) ^ d := by
          simp_rw [mul_assoc]
          rw [← mul_sum]
          congr 1
          rw [add_pow, ← Fin.sum_univ_eq_sum_range]
          apply sum_congr rfl
          intro i _
          ring

private lemma one_norm_bound {p R : ℝ} (hp : 0 < p) (hR : 0 ≤ R)
    (hsmall : 2 * R ≤ p) {w : ℂ} (hw : ‖w‖ ≤ R) :
    ‖(p : ℂ) + w‖ ≤ p + w.re + R ^ 2 / p := by
  have hre : -R ≤ w.re := by
    have := (abs_le.mp (Complex.abs_re_le_norm w)).1
    linarith
  have him : w.im ^ 2 ≤ R ^ 2 := by
    have := Complex.sq_norm_sub_sq_re w
    nlinarith [sq_nonneg w.re, norm_nonneg w]
  have hfrac : 0 ≤ R ^ 2 / p := div_nonneg (sq_nonneg _) hp.le
  have hcancel : (R ^ 2 / p) * p = R ^ 2 := div_mul_cancel₀ _ hp.ne'
  have hnorm := Complex.sq_norm_sub_sq_re ((p : ℂ) + w)
  simp only [add_re, ofReal_re, add_im, ofReal_im, zero_add] at hnorm
  have hright : 0 ≤ p + w.re + R ^ 2 / p := by linarith
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  nlinarith [mul_nonneg (show 0 ≤ p + 2 * w.re by linarith) hfrac,
    sq_nonneg (R ^ 2 / p)]

/-- The two foci of the Bernstein ellipse have a common quadratic disk bound,
including the degenerate endpoint regime. -/
lemma ellipse_disk_bound {p R : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hR : 0 < R) {z : ℂ} (hz : ‖z - (p : ℂ)‖ ≤ R) :
    ‖z‖ + ‖1 - z‖ ≤ 1 + 6 * R ^ 2 / (p * (1 - p) + R) := by
  let v := p * (1 - p)
  have hpzero := hp.1
  have hpone := hp.2
  have hv : 0 ≤ v := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hden : 0 < v + R := add_pos_of_nonneg_of_pos hv hR
  by_cases hnear : 2 * R ≤ v
  · have hvpos : 0 < v := by linarith
    have hpR : 2 * R ≤ p := by
      have h := mul_le_mul_of_nonneg_left (show 1 - p ≤ 1 by linarith) hp.1
      dsimp [v] at hnear
      nlinarith
    have hqR : 2 * R ≤ 1 - p := by
      have h := mul_le_mul_of_nonneg_right hp.2 (sub_nonneg.mpr hp.2)
      dsimp [v] at hnear
      nlinarith
    have hp0 : 0 < p := by linarith
    have hq0 : 0 < 1 - p := by linarith
    have h1 := one_norm_bound hp0 hR.le hpR hz
    have h2 := one_norm_bound hq0 hR.le hqR (w := -(z - (p : ℂ))) (by rw [norm_neg]; exact hz)
    have he1 : (p : ℂ) + (z - (p : ℂ)) = z := by ring
    have he2 : ((1 - p : ℝ) : ℂ) + -(z - (p : ℂ)) = 1 - z := by push_cast; ring
    rw [he1] at h1
    rw [he2] at h2
    simp only [neg_re] at h2
    have he : R ^ 2 / p + R ^ 2 / (1 - p) = R ^ 2 / v := by
      dsimp [v]; field_simp; ring
    have hsum : ‖z‖ + ‖1 - z‖ ≤ 1 + R ^ 2 / v := by linarith
    refine hsum.trans ?_
    apply add_le_add_right
    apply (div_le_div_iff₀ hvpos hden).mpr
    nlinarith [sq_nonneg R]
  · have hz1 : ‖z‖ ≤ p + R := by
      calc
        ‖z‖ = ‖(p : ℂ) + (z - (p : ℂ))‖ := by congr 1; ring
        _ ≤ ‖(p : ℂ)‖ + ‖z - (p : ℂ)‖ := norm_add_le _ _
        _ ≤ p + R := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1]
          exact add_le_add_right hz p
    have hz2 : ‖1 - z‖ ≤ 1 - p + R := by
      calc
        ‖1 - z‖ = ‖((1 - p : ℝ) : ℂ) - (z - (p : ℂ))‖ := by push_cast; congr 1; ring
        _ ≤ ‖((1 - p : ℝ) : ℂ)‖ + ‖z - (p : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 - p + R := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp.2)]
          exact add_le_add_right hz (1-p)
    have hratio : 2 * R ≤ 6 * R ^ 2 / (v + R) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    linarith

/-- The radius adapts to the derivative order and to both endpoints. -/
def derivativeRadius (d ℓ : ℕ) (p : ℝ) : ℝ :=
  max (Real.sqrt ((ℓ : ℝ) * (p * (1 - p)) / d)) ((ℓ : ℝ) / d)

lemma radius_properties {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 < derivativeRadius d ℓ p ∧
      (derivativeRadius d ℓ p) ^ 2 / (p * (1 - p) + derivativeRadius d ℓ p)
        ≤ (ℓ : ℝ) / d := by
  let ε : ℝ := (ℓ : ℝ) / d
  let v := p * (1 - p)
  have he : 0 < ε := div_pos (by exact_mod_cast hℓ) (by exact_mod_cast hd)
  have hv : 0 ≤ v := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have heq : derivativeRadius d ℓ p = max (Real.sqrt (ε * v)) ε := by
    simp only [derivativeRadius, ε, v, div_mul_eq_mul_div]
  rw [heq]
  have hpos : 0 < max (Real.sqrt (ε * v)) ε := he.trans_le (le_max_right _ _)
  refine ⟨hpos, (div_le_iff₀ (add_pos_of_nonneg_of_pos hv hpos)).mpr ?_⟩
  have hs := Real.sq_sqrt (mul_nonneg he.le hv)
  rcases le_total (Real.sqrt (ε * v)) ε with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonneg he.le hv]
  · rw [max_eq_left h]
    nlinarith [Real.sqrt_nonneg (ε * v)]

lemma bernstein_disk_bound {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    (c : Fin (d + 1) → ℂ) {B p : ℝ} (hc : ∀ i, ‖c i‖ ≤ B)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) {z : ℂ}
    (hz : ‖z - (p : ℂ)‖ ≤ derivativeRadius d ℓ p) :
    ‖(bernsteinRealization d c).eval z‖ ≤ B * Real.exp (6 * (ℓ : ℝ)) := by
  obtain ⟨hR, hratio⟩ := radius_properties hd hℓ hp
  have hB : 0 ≤ B := (norm_nonneg (c ⟨0, by omega⟩)).trans (hc _)
  have hgeo := ellipse_disk_bound hp hR hz
  rw [mul_div_assoc] at hgeo
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs : ‖z‖ + ‖1 - z‖ ≤ 1 + 6 * ((ℓ : ℝ) / d) := by linarith
  have he : (1 + 6 * ((ℓ : ℝ) / d)) ^ d ≤ Real.exp (6 * (ℓ : ℝ)) := by
    have h := Real.add_one_le_exp (6 * ((ℓ : ℝ) / d))
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 6 * ((ℓ : ℝ) / d))
      (by linarith : 1 + 6 * ((ℓ : ℝ) / d) ≤ Real.exp (6 * ((ℓ : ℝ) / d))) d
    rw [← Real.exp_nat_mul] at hpow
    have heq : (d : ℝ) * (6 * ((ℓ : ℝ) / d)) = 6 * (ℓ : ℝ) := by
      field_simp
    rwa [heq] at hpow
  exact (original_coefficients_bound d c hc z).trans
    (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (by positivity) hs d).trans he) hB)

lemma polynomial_iterated_deriv (P : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => P.eval z) = fun z => (derivative^[n] P).eval z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext z
    rw [Polynomial.deriv, Function.iterate_succ_apply']

lemma coefficient_cauchy_bound (P : ℂ[X]) (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : ∀ z : ℂ, ‖z‖ = R → ‖P.eval z‖ ≤ M) :
    ‖P.coeff n‖ ≤ M / R ^ n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun z : ℂ => P.eval z) (c := 0) n hR P.differentiable.diffContOnCl
    (fun z hz => hM z (by simpa [dist_eq_norm] using hz))
  have heq : iteratedDeriv n (fun z : ℂ => P.eval z) 0 =
      (n.factorial : ℂ) * P.coeff n := by
    rw [polynomial_iterated_deriv]
    change (derivative^[n] P).eval 0 = _
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [Nat.descFactorial_self, nsmul_eq_mul]
  rw [heq, norm_mul, Complex.norm_natCast] at h
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h' : (n.factorial : ℝ) * ‖P.coeff n‖ ≤ (n.factorial : ℝ) * (M / R ^ n) := by
    simpa [mul_div_assoc] using h
  nlinarith

private lemma bernstein_taylor_coefficient_bound {d ℓ : ℕ} (hd : 0 < d)
    (hℓ : 0 < ℓ) (c : Fin (d + 1) → ℂ) {B p : ℝ}
    (hc : ∀ i, ‖c i‖ ≤ B) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ‖((bernsteinRealization d c).taylor (p : ℂ)).coeff ℓ‖ ≤
      B * (Real.exp 6 / derivativeRadius d ℓ p) ^ ℓ := by
  have hR := (radius_properties hd hℓ hp).1
  have h := coefficient_cauchy_bound ((bernsteinRealization d c).taylor (p : ℂ)) ℓ hR
    (fun z hz => by
      rw [taylor_eval]
      apply bernstein_disk_bound hd hℓ c hc hp
      simpa using hz.le)
  rw [show 6 * (ℓ : ℝ) = (ℓ : ℝ) * 6 by ring, Real.exp_nat_mul] at h
  simpa [div_pow, mul_div_assoc] using h

private lemma norm_one_add_le_gaussian (z : ℂ) :
    ‖1 + z‖ ≤ Real.exp (z.re + ‖z‖ ^ 2 / 2) := by
  have hn : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im,
      one_re, one_im]
    ring
  have he := Real.add_one_le_exp (2 * z.re + ‖z‖ ^ 2)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [hn, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (z.re + ‖z‖ ^ 2 / 2) = 2 * z.re + ‖z‖ ^ 2 by ring]
  linarith

/-- The centered population generating polynomial; its coefficient divided
by `choose D ℓ` is the mean product over all subsets of size `ℓ`. -/
def populationGenerating (D : ℕ) (y : Fin D → ℝ) : ℂ[X] :=
  ∏ i : Fin D, (1 + C (y i : ℂ) * X)

private lemma population_gaussian_bound {D : ℕ} (y : Fin D → ℝ)
    (hcenter : ∑ i, y i = 0) (z : ℂ) :
    ‖(populationGenerating D y).eval z‖ ≤
      Real.exp ((∑ i, (y i) ^ 2) * ‖z‖ ^ 2 / 2) := by
  calc
    ‖(populationGenerating D y).eval z‖ = ∏ i : Fin D, ‖1 + (y i : ℂ) * z‖ := by
      simp [populationGenerating, eval_prod, norm_prod]
    _ ≤ ∏ i : Fin D, Real.exp (((y i : ℂ) * z).re + ‖(y i : ℂ) * z‖ ^ 2 / 2) := by
      apply prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_one_add_le_gaussian _)
    _ = Real.exp ((∑ i, (y i) ^ 2) * ‖z‖ ^ 2 / 2) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [sum_add_distrib, ← sum_mul, hcenter, zero_mul, zero_add]
      simp_rw [div_eq_mul_inv]
      rw [← sum_mul, ← sum_mul]

private lemma population_coefficient_bound {D : ℕ} (y : Fin D → ℝ)
    (hcenter : ∑ i, y i = 0) (ℓ : ℕ) {R : ℝ} (hR : 0 < R) :
    ‖(populationGenerating D y).coeff ℓ‖ ≤
      Real.exp ((∑ i, (y i) ^ 2) * R ^ 2 / 2) / R ^ ℓ := by
  apply coefficient_cauchy_bound _ ℓ hR
  intro z hz
  simpa [hz] using population_gaussian_bound y hcenter z

private lemma choose_power_lower {D ℓ : ℕ} (hℓ : 0 < ℓ) (hD : ℓ ≤ D) :
    ((D : ℝ) / ℓ) ^ ℓ ≤ (D.choose ℓ : ℝ) := by
  have hlR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hprod : ∏ i ∈ range ℓ, ((D : ℝ) - i) / ((ℓ : ℝ) - i) =
      (D.choose ℓ : ℝ) := by
    rw [prod_div_distrib]
    have hnum : ∏ i ∈ range ℓ, ((D : ℝ) - i) = (D.descFactorial ℓ : ℝ) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply prod_congr rfl
      intro i hi
      have hiℓ := mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ D)]
    have hden : ∏ i ∈ range ℓ, ((ℓ : ℝ) - i) = (ℓ.factorial : ℝ) := by
      rw [← Nat.descFactorial_self ℓ, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply prod_congr rfl
      intro i hi
      have hiℓ := mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ ℓ)]
    rw [hnum, hden, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero ℓ)
  calc
    ((D : ℝ) / ℓ) ^ ℓ = ∏ i ∈ range ℓ, ((D : ℝ) / ℓ) := by simp [div_pow]
    _ ≤ ∏ i ∈ range ℓ, ((D : ℝ) - i) / ((ℓ : ℝ) - i) := by
      apply prod_le_prod₀ (fun i _ => by positivity)
      intro i hi
      have hiℓ : i < ℓ := mem_range.mp hi
      have hiR : (i : ℝ) < ℓ := by exact_mod_cast hiℓ
      apply (div_le_div_iff₀ hlR (by linarith : 0 < (ℓ : ℝ) - i)).mpr
      have hdR : (ℓ : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith [show 0 ≤ (i : ℝ) by positivity]
    _ = (D.choose ℓ : ℝ) := hprod

/-- The exact finite-population product moment, normalized by the number of subsets. -/
def populationProductMoment (D : ℕ) (y : Fin D → ℝ) (ℓ : ℕ) : ℂ :=
  (populationGenerating D y).coeff ℓ / (D.choose ℓ : ℂ)

private lemma population_product_moment_bound {D ℓ : ℕ} (hℓ : 0 < ℓ) (hD : ℓ ≤ D)
    (y : Fin D → ℝ) (hcenter : ∑ i, y i = 0) :
    ‖populationProductMoment D y ℓ‖ ≤
      (Real.exp (1 / 2) * Real.sqrt (ℓ : ℝ) * Real.sqrt (∑ i, (y i) ^ 2) / D) ^ ℓ := by
  let V := ∑ i : Fin D, (y i) ^ 2
  have hV : 0 ≤ V := sum_nonneg (fun i _ => sq_nonneg _)
  have hlR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hdR : 0 < (D : ℝ) := by exact_mod_cast (hℓ.trans_le hD)
  have hchoose : 0 < (D.choose ℓ : ℝ) := by exact_mod_cast Nat.choose_pos hD
  by_cases hVz : V = 0
  · have hy : ∀ i, y i = 0 := by
      intro i
      have h := single_le_sum (fun j _ => sq_nonneg (y j)) (mem_univ i)
      change (y i) ^ 2 ≤ V at h
      rw [hVz] at h
      nlinarith [sq_nonneg (y i)]
    simp [populationProductMoment, populationGenerating, hy, coeff_one, show ℓ ≠ 0 by omega]
  · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hVz)
    let R := Real.sqrt (ℓ : ℝ) / Real.sqrt V
    have hR : 0 < R := div_pos (Real.sqrt_pos.mpr hlR) (Real.sqrt_pos.mpr hVp)
    have hR2 : V * R ^ 2 = ℓ := by
      dsimp [R]
      rw [div_pow, Real.sq_sqrt hlR.le, Real.sq_sqrt hV]
      field_simp
    have hb := population_coefficient_bound y hcenter ℓ hR
    change ‖(populationGenerating D y).coeff ℓ‖ ≤ Real.exp (V * R ^ 2 / 2) / R ^ ℓ at hb
    rw [hR2] at hb
    have he : Real.exp ((ℓ : ℝ) / 2) = Real.exp (1 / 2) ^ ℓ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he] at hb
    have hlower := choose_power_lower hℓ hD
    calc
      ‖populationProductMoment D y ℓ‖ = ‖(populationGenerating D y).coeff ℓ‖ /
          (D.choose ℓ : ℝ) := by simp [populationProductMoment]
      _ ≤ (Real.exp (1 / 2) ^ ℓ / R ^ ℓ) / ((D : ℝ) / ℓ) ^ ℓ := by
        exact div_le_div₀ (by positivity) hb (pow_pos (div_pos hdR hlR) ℓ) hlower
      _ = (Real.exp (1 / 2) * Real.sqrt (ℓ : ℝ) * Real.sqrt V / D) ^ ℓ := by
        rw [← div_pow, ← div_pow]
        congr 1
        dsimp [R]
        have hs := Real.sq_sqrt hlR.le
        field_simp
        nlinarith

/-- The centered binary population at output index `J`, including `J=0,D`. -/
def binaryPopulation (D J : ℕ) (i : Fin D) : ℝ :=
  (if (i : ℕ) < J then 1 else 0) - (J : ℝ) / D

private lemma binary_population_sum {D J : ℕ} (hD : 0 < D) (hJ : J ≤ D) :
    ∑ i : Fin D, binaryPopulation D J i = 0 := by
  have hones : ∑ i : Fin D, (if (i : ℕ) < J then (1 : ℝ) else 0) = J := by
    change (∑ i : Fin D, (fun k : ℕ => if k < J then (1 : ℝ) else 0) i.val) = J
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < J then (1 : ℝ) else 0) D]
    rw [show D = J + (D - J) by omega, sum_range_add]
    have hfirst : ∑ i ∈ range J, (if i < J then (1 : ℝ) else 0) = J := by
      calc
        _ = ∑ i ∈ range J, (1 : ℝ) := by
          apply sum_congr rfl
          intro i hi
          rw [if_pos (mem_range.mp hi)]
        _ = J := by simp
    have hlast : ∑ i ∈ range (D - J), (if J + i < J then (1 : ℝ) else 0) = 0 := by
      simp
    rw [hfirst, hlast, add_zero]
  simp only [binaryPopulation, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [hones]
  have hd0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp
  ring

private lemma binary_population_variance {D J : ℕ} (hD : 0 < D) (hJ : J ≤ D) :
    ∑ i : Fin D, (binaryPopulation D J i) ^ 2 =
      (D : ℝ) * ((J : ℝ) / D) * (1 - (J : ℝ) / D) := by
  have hsum := binary_population_sum hD hJ
  have hones : ∑ i : Fin D, (if (i : ℕ) < J then (1 : ℝ) else 0) = J := by
    simp only [binaryPopulation, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    have hd0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp at hsum
    exact sub_eq_zero.mp hsum
  calc
    ∑ i : Fin D, (binaryPopulation D J i) ^ 2 =
        ∑ i : Fin D, ((if (i : ℕ) < J then (1 : ℝ) else 0) *
          (1 - 2 * ((J : ℝ) / D)) + ((J : ℝ) / D) ^ 2) := by
      apply sum_congr rfl
      intro i _
      dsimp [binaryPopulation]
      split_ifs <;> ring
    _ = (D : ℝ) * ((J : ℝ) / D) * (1 - (J : ℝ) / D) := by
      rw [sum_add_distrib, ← sum_mul, hones]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring

/-- The actual binary-population centered product moments. -/
def centeredProductMoment (D J ℓ : ℕ) : ℂ :=
  populationProductMoment D (binaryPopulation D J) ℓ

private lemma centered_moment_bound {D J ℓ : ℕ} (hD : 0 < D) (hJ : J ≤ D)
    (hℓ : 0 < ℓ) (hℓD : ℓ ≤ D) :
    ‖centeredProductMoment D J ℓ‖ ≤
      (Real.exp (1 / 2) * Real.sqrt (ℓ : ℝ) *
        Real.sqrt ((D : ℝ) * ((J : ℝ) / D) * (1 - (J : ℝ) / D)) / D) ^ ℓ := by
  have h := population_product_moment_bound hℓ hℓD (binaryPopulation D J)
    (binary_population_sum hD hJ)
  rwa [binary_population_variance hD hJ] at h

private lemma binary_fraction_mem {D J : ℕ} (hD : 0 < D) (hJ : J ≤ D) :
    (J : ℝ) / D ∈ Set.Icc (0 : ℝ) 1 := by
  have hdR : 0 < (D : ℝ) := by exact_mod_cast hD
  refine ⟨by positivity, (div_le_one hdR).mpr (by exact_mod_cast hJ)⟩

private lemma radius_moment_comparison {d D ℓ : ℕ} (hd : 0 < d) (hD : 0 < D)
    (hℓ : 0 < ℓ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (ℓ : ℝ) * Real.sqrt ((D : ℝ) * p * (1 - p)) / D ≤
      Real.sqrt ((d : ℝ) / D) * derivativeRadius d ℓ p := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hv : 0 ≤ p * (1 - p) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hroot : Real.sqrt ((ℓ : ℝ) * (p * (1 - p)) / d) ≤
      derivativeRadius d ℓ p := le_max_left _ _
  have hRpos := (radius_properties hd hℓ hp).1
  have hR2 : (ℓ : ℝ) * (p * (1 - p)) / d ≤ (derivativeRadius d ℓ p) ^ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ (ℓ : ℝ) * (p * (1-p)) / d by positivity)
    nlinarith [Real.sqrt_nonneg ((ℓ : ℝ) * (p * (1-p)) / d)]
  have hmul := (div_le_iff₀ hdR).mp hR2
  have hdiv := (div_le_div_iff_of_pos_right hDR).mpr hmul
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (ℓ : ℝ)),
    Real.sq_sqrt (show 0 ≤ (D : ℝ) * p * (1-p) by
      have h := mul_nonneg (show 0 ≤ (D : ℝ) by positivity) hv
      nlinarith),
    Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ) / D)]
  convert hdiv using 1 <;> field_simp

private lemma taylor_moment_term_bound {d D J ℓ : ℕ} (hd : 0 < d)
    (hD : 0 < D) (hJ : J ≤ D) (hℓ : 0 < ℓ) (hℓD : ℓ ≤ D)
    (c : Fin (d + 1) → ℂ) {B : ℝ} (hc : ∀ i, ‖c i‖ ≤ B) :
    ‖((bernsteinRealization d c).taylor ((J : ℂ) / D)).coeff ℓ *
      centeredProductMoment D J ℓ‖ ≤
      B * (Real.exp (13 / 2) * Real.sqrt ((d : ℝ) / D)) ^ ℓ := by
  let p : ℝ := (J : ℝ) / D
  have hp := binary_fraction_mem hD hJ
  have hB : 0 ≤ B := (norm_nonneg (c ⟨0, by omega⟩)).trans (hc _)
  have hR := (radius_properties hd hℓ hp).1
  have hcauchy := bernstein_taylor_coefficient_bound hd hℓ c hc hp
  have hmoment := centered_moment_bound hD hJ hℓ hℓD
  have hscale := radius_moment_comparison hd hD hℓ hp
  have hpC : (p : ℂ) = (J : ℂ) / D := by simp [p]
  rw [hpC] at hcauchy
  rw [norm_mul]
  calc
    _ ≤ (B * (Real.exp 6 / derivativeRadius d ℓ p) ^ ℓ) *
        (Real.exp (1/2) * Real.sqrt (ℓ : ℝ) *
          Real.sqrt ((D : ℝ) * p * (1-p)) / D) ^ ℓ :=
      mul_le_mul hcauchy hmoment (norm_nonneg _) (by positivity)
    _ = B * ((Real.exp 6 / derivativeRadius d ℓ p) *
        (Real.exp (1/2) * Real.sqrt (ℓ : ℝ) *
          Real.sqrt ((D : ℝ) * p * (1-p)) / D)) ^ ℓ := by rw [mul_assoc, mul_pow]
    _ ≤ B * (Real.exp (13/2) * Real.sqrt ((d : ℝ) / D)) ^ ℓ := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply pow_le_pow_left₀ (by positivity)
      have he : Real.exp (13/2) = Real.exp 6 * Real.exp (1/2) := by
        rw [← Real.exp_add]
        congr 1
        norm_num
      rw [he]
      have hs := mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (Real.exp_pos 6).le (Real.exp_pos (1/2)).le)
      change Real.exp 6 * Real.exp (1/2) *
        (Real.sqrt (ℓ : ℝ) * Real.sqrt ((D : ℝ) * p * (1-p)) / D) ≤
        Real.exp 6 * Real.exp (1/2) * (Real.sqrt ((d : ℝ) / D) * derivativeRadius d ℓ p) at hs
      calc
        _ = (Real.exp 6 * Real.exp (1/2) *
            (Real.sqrt (ℓ : ℝ) * Real.sqrt ((D : ℝ) * p * (1-p)) / D)) /
              derivativeRadius d ℓ p := by ring
        _ ≤ Real.exp 6 * Real.exp (1/2) * Real.sqrt ((d : ℝ) / D) := by
          apply (div_le_iff₀ hR).mpr
          nlinarith [hs]

/-- The degree `D` Bernstein coefficient transform, interpreted for polynomials
of degree at most `D`. -/
def bernsteinCoefficient (D J : ℕ) (P : ℂ[X]) : ℂ :=
  ∑ k ∈ range (D + 1), P.coeff k * (J.choose k : ℂ) / (D.choose k : ℂ)

lemma bernstein_coefficient_sum {ι : Type*} (s : Finset ι)
    (P : ι → ℂ[X]) (D J : ℕ) :
    bernsteinCoefficient D J (∑ i ∈ s, P i) = ∑ i ∈ s, bernsteinCoefficient D J (P i) := by
  simp only [bernsteinCoefficient, finsetSum_coeff, sum_mul, sum_div]
  rw [sum_comm]

lemma bernstein_coefficient_C_mul (D J : ℕ) (a : ℂ) (P : ℂ[X]) :
    bernsteinCoefficient D J (C a * P) = a * bernsteinCoefficient D J P := by
  simp only [bernsteinCoefficient, coeff_C_mul, mul_sum, mul_div_assoc, mul_assoc]

private lemma binary_generating_formula {D J : ℕ} (hJ : J ≤ D) :
    populationGenerating D (binaryPopulation D J) =
      (1 + C (1 - (J : ℂ) / D) * X) ^ J *
        (1 + C (-(J : ℂ) / D) * X) ^ (D - J) := by
  rw [populationGenerating]
  simp only [binaryPopulation]
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ =>
    1 + C (Complex.ofReal ((if k < J then (1 : ℝ) else 0) - (J : ℝ) / D)) * X) D]
  nth_rw 1 [show D = J + (D - J) by omega]
  rw [prod_range_add]
  have hfirst : ∏ i ∈ range J,
      (1 + C (Complex.ofReal ((if i < J then (1 : ℝ) else 0) - (J : ℝ) / D)) * X) =
      (1 + C (1 - (J : ℂ) / D) * X) ^ J := by
    convert prod_const (1 + C (1 - (J : ℂ) / D) * X) using 1
    · apply prod_congr rfl
      intro i hi
      rw [if_pos (mem_range.mp hi)]
      push_cast
      rfl
    · simp
  have hlast : ∏ i ∈ range (D - J),
      (1 + C (Complex.ofReal ((if J + i < J then (1 : ℝ) else 0) - (J : ℝ) / D)) * X) =
      (1 + C (-(J : ℂ) / D) * X) ^ (D - J) := by
    simp only [show ∀ i : ℕ, ¬J + i < J by omega, ite_false, zero_sub]
    push_cast
    simp [neg_div]
  exact congrArg₂ (· * ·) hfirst hlast

private lemma binary_generating_expansion {D J : ℕ} (hJ : J ≤ D) :
    populationGenerating D (binaryPopulation D J) =
      ∑ k ∈ range (J + 1), C (J.choose k : ℂ) * X ^ k *
        (1 + C (-(J : ℂ) / D) * X) ^ (D - k) := by
  rw [binary_generating_formula hJ]
  let A : ℂ[X] := 1 + C (-(J : ℂ) / D) * X
  have he : 1 + C (1 - (J : ℂ) / D) * X = X + A := by
    dsimp [A]
    simp only [map_sub, map_one, neg_div, map_neg]
    ring
  rw [he, add_pow, sum_mul]
  apply sum_congr rfl
  intro k hk
  have hkJ : k ≤ J := by have := mem_range.mp hk; omega
  have hepow : D - k = J - k + (D - J) := by omega
  rw [hepow, pow_add]
  simp only [C_eq_natCast]
  dsimp [A]
  ring

private lemma linear_binomial_coeff (a : ℂ) (n k : ℕ) :
    ((1 + C a * X) ^ n).coeff k = a ^ k * (n.choose k : ℂ) := by
  have he : 1 + C a * X = (X + 1).comp (C a * X) := by simp [add_comm]
  rw [he, ← pow_comp, comp_C_mul_X_coeff, coeff_X_add_one_pow]
  ring

private lemma binary_generating_coefficient {D J ℓ : ℕ} (hJ : J ≤ D) :
    (populationGenerating D (binaryPopulation D J)).coeff ℓ =
      ∑ k ∈ range (ℓ + 1), (J.choose k : ℂ) *
        (-(J : ℂ) / D) ^ (ℓ - k) * ((D - k).choose (ℓ - k) : ℂ) := by
  rw [binary_generating_expansion hJ, finsetSum_coeff]
  have hterm (k : ℕ) :
      (C (J.choose k : ℂ) * X ^ k *
        (1 + C (-(J : ℂ) / D) * X) ^ (D - k)).coeff ℓ =
      if k ≤ ℓ then (J.choose k : ℂ) * (-(J : ℂ) / D) ^ (ℓ-k) *
        ((D-k).choose (ℓ-k) : ℂ) else 0 := by
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', linear_binomial_coeff]
    split_ifs <;> ring
  simp_rw [hterm]
  apply sum_congr_of_eq_on_inter
  · intro k hk hknot
    have hkℓ : ℓ < k := by simpa [mem_range] using hknot
    simp [not_le.mpr hkℓ]
  · intro k hk hknot
    have hkJ : J < k := by simpa [mem_range] using hknot
    simp [Nat.choose_eq_zero_of_lt hkJ]
  · intro k hk1 hk2
    have hkℓ : k ≤ ℓ := by have := mem_range.mp hk2; omega
    simp [hkℓ]

private lemma centered_coefficient_identity {D J ℓ : ℕ} (hJ : J ≤ D) (hℓ : ℓ ≤ D) :
    bernsteinCoefficient D J ((X - C ((J : ℂ) / D)) ^ ℓ) =
      centeredProductMoment D J ℓ := by
  have hchoose : (D.choose ℓ : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hℓ).ne'
  rw [centeredProductMoment, populationProductMoment,
    binary_generating_coefficient hJ]
  simp only [bernsteinCoefficient, sub_eq_add_neg, ← map_neg, coeff_X_add_C_pow, neg_div]
  rw [sum_div]
  have hshort : ∑ k ∈ range (D + 1),
      ((-(J : ℂ) / D) ^ (ℓ-k) * (ℓ.choose k : ℂ)) * (J.choose k : ℂ) /
        (D.choose k : ℂ) =
      ∑ k ∈ range (ℓ + 1),
        ((-(J : ℂ) / D) ^ (ℓ-k) * (ℓ.choose k : ℂ)) * (J.choose k : ℂ) /
          (D.choose k : ℂ) := by
    symm
    apply sum_subset (range_mono (by omega : ℓ + 1 ≤ D + 1))
    intro k hk hknot
    have hkℓ : ℓ < k := by simpa [mem_range] using hknot
    simp [Nat.choose_eq_zero_of_lt hkℓ]
  simp only [neg_div] at hshort
  rw [hshort]
  apply sum_congr rfl
  intro k hk
  have hkℓ : k ≤ ℓ := by have := mem_range.mp hk; omega
  have hkD : k ≤ D := hkℓ.trans hℓ
  have hkchoose : (D.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkD).ne'
  have hbin : (D.choose ℓ : ℂ) * (ℓ.choose k : ℂ) =
      (D.choose k : ℂ) * ((D-k).choose (ℓ-k) : ℂ) := by exact_mod_cast Nat.choose_mul hkℓ
  field_simp
  linear_combination ((J.choose k : ℂ) * (-(J : ℂ) / D) ^ (ℓ-k)) * hbin

lemma realization_degree (d : ℕ) (c : Fin (d + 1) → ℂ) :
    (bernsteinRealization d c).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  calc
    (C (c i) * bernsteinPolynomial ℂ d i).natDegree ≤
        (C (c i)).natDegree + (bernsteinPolynomial ℂ d i).natDegree := natDegree_mul_le
    _ ≤ d := by
      rw [natDegree_C, zero_add]
      dsimp [bernsteinPolynomial]
      rw [mul_assoc]
      calc
        _ ≤ (d.choose (i : ℕ) : ℂ[X]).natDegree +
          ((X : ℂ[X]) ^ (i : ℕ) * (1 - X : ℂ[X]) ^ (d - (i : ℕ))).natDegree := natDegree_mul_le
        _ ≤ d := by
          simp only [natDegree_natCast, zero_add]
          have h1 := natDegree_mul_le (p := (X : ℂ[X]) ^ (i : ℕ))
            (q := (1 - X : ℂ[X]) ^ (d - (i : ℕ)))
          have h2 := natDegree_pow_le (p := (1 - X : ℂ[X])) (n := d - (i : ℕ))
          have h3 : (1 - X : ℂ[X]).natDegree ≤ 1 := by
            calc
              _ ≤ max (1 : ℂ[X]).natDegree (X : ℂ[X]).natDegree := natDegree_sub_le _ _
              _ ≤ 1 := by simp
          simp only [natDegree_X_pow] at h1
          have h4 := Nat.mul_le_mul_left (d - (i : ℕ)) h3
          have hiD : (i : ℕ) ≤ d := by omega
          omega

/-- The ordinary Taylor polynomial through order `r` at `p`. -/
def truncatedTaylor (P : ℂ[X]) (p : ℂ) (r : ℕ) : ℂ[X] :=
  ∑ ℓ ∈ range (r + 1), C ((P.taylor p).coeff ℓ) * (X - C p) ^ ℓ

lemma taylor_expansion_up_to (P : ℂ[X]) (p : ℂ) {d : ℕ}
    (hdeg : P.natDegree ≤ d) :
    P = ∑ ℓ ∈ range (d + 1), C ((P.taylor p).coeff ℓ) * (X - C p) ^ ℓ := by
  have h := (P.taylor p).as_sum_range_C_mul_X_pow' (n := d + 1)
    (by rw [natDegree_taylor]; omega)
  apply_fun (fun Q : ℂ[X] => Q.comp (X - C p)) at h
  have hleft : (P.taylor p).comp (X - C p) = P := by
    rw [sub_eq_add_neg, ← map_neg, ← taylor_apply, taylor_taylor]
    simp
  rw [hleft] at h
  simpa [Polynomial.sum_comp] using h

lemma taylor_remainder_expansion (P : ℂ[X]) (p : ℂ) {d r : ℕ}
    (hdeg : P.natDegree ≤ d) (hr : r ≤ d) :
    P - truncatedTaylor P p r =
      ∑ ℓ ∈ Ico (r + 1) (d + 1), C ((P.taylor p).coeff ℓ) * (X - C p) ^ ℓ := by
  nth_rw 1 [taylor_expansion_up_to P p hdeg]
  unfold truncatedTaylor
  have h := sum_range_add_sum_Ico
    (fun ℓ => C ((P.taylor p).coeff ℓ) * (X - C p) ^ ℓ)
    (by omega : r + 1 ≤ d + 1)
  rw [← h]
  abel

/-- A single geometric factor controls all derivative orders and all output
indices in the centered Taylor coefficient remainder. -/
private lemma taylor_coefficient_remainder_geometric {d D J r : ℕ} (hd : 0 < d)
    (hdD : d ≤ D) (hJ : J ≤ D) (hr : r ≤ d) (c : Fin (d + 1) → ℂ)
    (hsmall : Real.exp (13 / 2) * Real.sqrt ((d : ℝ) / D) ≤ 1 / 2) :
    ‖bernsteinCoefficient D J (bernsteinRealization d c -
      truncatedTaylor (bernsteinRealization d c) ((J : ℂ) / D) r)‖ ≤
        2 * ‖c‖ * (Real.exp (13 / 2) * Real.sqrt ((d : ℝ) / D)) ^ (r + 1) := by
  have hD : 0 < D := hd.trans_le hdD
  let q := Real.exp (13/2) * Real.sqrt ((d : ℝ) / D)
  have hq : 0 ≤ q := by positivity
  have hqone : q < 1 := by dsimp [q]; linarith
  rw [taylor_remainder_expansion _ _ (realization_degree d c) hr,
    bernstein_coefficient_sum]
  have hterms : ∀ ℓ ∈ Ico (r + 1) (d + 1),
      ‖bernsteinCoefficient D J (C (((bernsteinRealization d c).taylor
        ((J : ℂ) / D)).coeff ℓ) * (X - C ((J : ℂ) / D)) ^ ℓ)‖ ≤ ‖c‖ * q ^ ℓ := by
    intro ℓ hℓ
    have hlower := (mem_Ico.mp hℓ).1
    have hupper := (mem_Ico.mp hℓ).2
    rw [bernstein_coefficient_C_mul, centered_coefficient_identity hJ (by omega)]
    exact taylor_moment_term_bound hd hD hJ (by omega) (by omega) c
      (fun i => norm_le_pi_norm c i)
  calc
    _ ≤ ∑ ℓ ∈ Ico (r + 1) (d + 1),
        ‖bernsteinCoefficient D J (C (((bernsteinRealization d c).taylor
          ((J : ℂ) / D)).coeff ℓ) * (X - C ((J : ℂ) / D)) ^ ℓ)‖ := norm_sum_le _ _
    _ ≤ ∑ ℓ ∈ Ico (r + 1) (d + 1), ‖c‖ * q ^ ℓ := sum_le_sum hterms
    _ = ‖c‖ * ∑ ℓ ∈ Ico (r + 1) (d + 1), q ^ ℓ := (mul_sum _ _ _).symm
    _ ≤ ‖c‖ * (q ^ (r + 1) / (1 - q)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq hqone) (norm_nonneg _)
    _ ≤ 2 * ‖c‖ * q ^ (r + 1) := by
      have hden : 0 < 1 - q := by linarith
      have hs : q ≤ 1/2 := hsmall
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      have hb : 0 ≤ ‖c‖ * q ^ (r + 1) := mul_nonneg (norm_nonneg _) (pow_nonneg hq _)
      nlinarith [mul_nonneg hb (show 0 ≤ 1/2-q by linarith)]

/-- A Taylor truncation of a polynomial of degree at most `r` is exact. -/
lemma truncated_taylor_exact (P : ℂ[X]) (p : ℂ) {r : ℕ}
    (hdeg : P.natDegree ≤ r) : truncatedTaylor P p r = P :=
  (taylor_expansion_up_to P p hdeg).symm

/-- The high-degree Bernstein coefficient remainder of the ordinary Taylor
polynomial has order `(d/D)^((r+1)/2)`, with constants depending only on `r`.
The input is the original normalized coefficient array, and `J=0,D` are included. -/
lemma taylor_coefficient_remainder_bound (r : ℕ) :
    ∃ A K : ℝ, 1 ≤ A ∧ 1 ≤ K ∧
      ∀ d D : ℕ, 0 < d → A * (d : ℝ) ≤ D →
        ∀ c : Fin (d + 1) → ℂ, ∀ J : ℕ, J ≤ D →
          ‖bernsteinCoefficient D J (bernsteinRealization d c -
            truncatedTaylor (bernsteinRealization d c) ((J : ℂ) / D) r)‖ ≤
            K * ((d : ℝ) / D) ^ (((r : ℝ) + 1) / 2) * ‖c‖ := by
  let E : ℝ := Real.exp (13/2)
  let A : ℝ := 4 * E ^ 2
  let K : ℝ := 2 * E ^ (r + 1)
  have hE : 1 ≤ E := Real.one_le_exp (by norm_num)
  have hEpos : 0 < E := Real.exp_pos _
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hK : 1 ≤ K := by
    have hpow : 1 ≤ E ^ (r + 1) := one_le_pow₀ hE
    dsimp [K]
    linarith
  refine ⟨A, K, hA, hK, ?_⟩
  intro d D hd hlarge c J hJ
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdD : d ≤ D := by
    have h := mul_le_mul_of_nonneg_right hA hdR.le
    norm_num only [one_mul] at h
    exact_mod_cast h.trans hlarge
  have hD : 0 < D := hd.trans_le hdD
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  by_cases hr : r ≤ d
  · have hs : E * Real.sqrt ((d : ℝ) / D) ≤ 1/2 := by
      have hsq : E ^ 2 * ((d : ℝ) / D) ≤ 1/4 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hDR).mpr
        dsimp [A] at hlarge
        nlinarith
      have heq : (E * Real.sqrt ((d : ℝ) / D)) ^ 2 = E ^ 2 * ((d : ℝ) / D) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hpos : 0 ≤ E * Real.sqrt ((d : ℝ) / D) := by positivity
      nlinarith
    have h := taylor_coefficient_remainder_geometric hd hdD hJ hr c hs
    have hpower : (Real.sqrt ((d : ℝ) / D)) ^ (r + 1) =
        ((d : ℝ) / D) ^ (((r : ℝ) + 1) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
      congr 1
      push_cast
      ring
    have heq : 2 * ‖c‖ * (E * Real.sqrt ((d : ℝ) / D)) ^ (r + 1) =
        K * ((d : ℝ) / D) ^ (((r : ℝ) + 1) / 2) * ‖c‖ := by
      rw [mul_pow, hpower]
      dsimp [K]
      ring
    exact h.trans_eq heq
  · have hdeg := (realization_degree d c).trans (by omega : d ≤ r)
    rw [truncated_taylor_exact _ _ hdeg, sub_self]
    simp only [bernsteinCoefficient, coeff_zero, zero_mul, zero_div, sum_const_zero, norm_zero]
    positivity

private lemma bernstein_monomial_term {D J k : ℕ} (hkJ : k ≤ J) (hJD : J ≤ D) :
    C ((J.choose k : ℂ) / (D.choose k : ℂ)) * bernsteinPolynomial ℂ D J =
      X ^ k * bernsteinPolynomial ℂ (D - k) (J - k) := by
  have hkD := hkJ.trans hJD
  have hchoose : (D.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkD).ne'
  have hbin : (D.choose J : ℂ) * (J.choose k : ℂ) =
      (D.choose k : ℂ) * ((D-k).choose (J-k) : ℂ) := by
    exact_mod_cast Nat.choose_mul hkJ
  have hscalar : ((J.choose k : ℂ) / (D.choose k : ℂ)) * (D.choose J : ℂ) =
      ((D-k).choose (J-k) : ℂ) := by
    field_simp
    linear_combination hbin
  have hexp : D-k-(J-k) = D-J := by omega
  have hexpX : J = k + (J-k) := by omega
  simp only [bernsteinPolynomial, ← C_eq_natCast]
  rw [mul_assoc, ← mul_assoc (C _) (C _), ← C_mul, hscalar, hexp, hexpX, pow_add]
  simp only [Nat.add_sub_cancel_left]
  ring

private lemma bernstein_monomial_reconstruction {D k : ℕ} (hk : k ≤ D) :
    (∑ J ∈ range (D + 1), C ((J.choose k : ℂ) / (D.choose k : ℂ)) *
      bernsteinPolynomial ℂ D J) = (X : ℂ[X]) ^ k := by
  have heD : D + 1 = k + (D - k + 1) := by omega
  rw [heD, sum_range_add]
  have hfirst : ∑ J ∈ range k, C ((J.choose k : ℂ) / (D.choose k : ℂ)) *
      bernsteinPolynomial ℂ D J = 0 := by
    apply sum_eq_zero
    intro J hJ
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hJ)]
  rw [hfirst, zero_add]
  calc
    _ = ∑ j ∈ range (D - k + 1), X ^ k * bernsteinPolynomial ℂ (D-k) j := by
      apply sum_congr rfl
      intro j hj
      have hjD : k + j ≤ D := by have := mem_range.mp hj; omega
      simpa using bernstein_monomial_term (Nat.le_add_right k j) hjD
    _ = X ^ k * ∑ j ∈ range (D-k+1), bernsteinPolynomial ℂ (D-k) j := by rw [mul_sum]
    _ = X ^ k := by rw [bernsteinPolynomial.sum, mul_one]

lemma bernstein_reconstruction (P : ℂ[X]) (D : ℕ) (hdeg : P.natDegree ≤ D) :
    (∑ J ∈ range (D+1), C (bernsteinCoefficient D J P) * bernsteinPolynomial ℂ D J) = P := by
  simp only [bernsteinCoefficient, map_sum, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ k ∈ range (D+1), C (P.coeff k) *
        (∑ J ∈ range (D+1), C ((J.choose k : ℂ) / (D.choose k : ℂ)) *
          bernsteinPolynomial ℂ D J) := by
      apply sum_congr rfl
      intro k hk
      rw [mul_sum]
      apply sum_congr rfl
      intro J hJ
      rw [show P.coeff k * (J.choose k : ℂ) / (D.choose k : ℂ) =
        P.coeff k * ((J.choose k : ℂ) / (D.choose k : ℂ)) by ring, map_mul]
      ring
    _ = ∑ k ∈ range (D+1), C (P.coeff k) * X ^ k := by
      apply sum_congr rfl
      intro k hk
      rw [bernstein_monomial_reconstruction (by have := mem_range.mp hk; omega)]
    _ = P := (P.as_sum_range_C_mul_X_pow' (by omega : P.natDegree < D+1)).symm

lemma truncated_taylor_degree (P : ℂ[X]) (p : ℂ) (r : ℕ) :
    (truncatedTaylor P p r).natDegree ≤ r := by
  apply natDegree_sum_le_of_forall_le
  intro ℓ hℓ
  calc
    _ ≤ (C ((P.taylor p).coeff ℓ)).natDegree + ((X - C p) ^ ℓ).natDegree := natDegree_mul_le
    _ ≤ ℓ := by
      rw [natDegree_C, zero_add]
      have hlin : (X - C p : ℂ[X]).natDegree ≤ 1 :=
        (natDegree_sub_le X (C p)).trans (by simp)
      exact (natDegree_pow_le_of_le ℓ hlin).trans_eq (Nat.mul_one ℓ)
    _ ≤ r := by have := mem_range.mp hℓ; omega

/-- At each output index `J`, the Taylor remainder centered at `J / D` has
an actual degree `D` Bernstein representation whose `J`th coefficient obeys
the common bound. Constants depend only on `r`, and both endpoints are included. -/
theorem taylor_coefficient_remainder (r : ℕ) :
    ∃ A K : ℝ, 1 ≤ A ∧ 1 ≤ K ∧
      ∀ d D : ℕ, 0 < d → A * (d : ℝ) ≤ D →
        ∀ c : Fin (d + 1) → ℂ, ∀ J : ℕ, (hJ : J ≤ D) →
          ∃ a : Fin (D + 1) → ℂ,
            bernsteinRealization d c - truncatedTaylor (bernsteinRealization d c)
              ((J : ℂ) / D) r = bernsteinRealization D a ∧
            ‖a ⟨J, by omega⟩‖ ≤ K * ((d : ℝ) / D) ^ (((r : ℝ) + 1) / 2) * ‖c‖ ∧
            (d ≤ r → a = 0) := by
  obtain ⟨A, K, hA, hK, h⟩ := taylor_coefficient_remainder_bound r
  refine ⟨A, K, hA, hK, ?_⟩
  intro d D hd hlarge c J hJ
  let P := bernsteinRealization d c
  let R := P - truncatedTaylor P ((J : ℂ) / D) r
  have hdD : d ≤ D := by
    have hmul := mul_le_mul_of_nonneg_right hA (show 0 ≤ (d : ℝ) by positivity)
    norm_num only [one_mul] at hmul
    exact_mod_cast hmul.trans hlarge
  have hRdeg : R.natDegree ≤ D := by
    by_cases hr : r ≤ D
    · exact (natDegree_sub_le _ _).trans
        (max_le ((realization_degree d c).trans hdD)
          ((truncated_taylor_degree _ _ _).trans hr))
    · have hzero : R = 0 := by
        dsimp [R]
        rw [truncated_taylor_exact _ _ ((realization_degree d c).trans (by omega)), sub_self]
      simp [hzero]
  refine ⟨fun j => bernsteinCoefficient D j R, ?_, h d D hd hlarge c J hJ, ?_⟩
  · change R = bernsteinRealization D (fun j => bernsteinCoefficient D j R)
    unfold bernsteinRealization
    rw [Fin.sum_univ_eq_sum_range (fun j => C (bernsteinCoefficient D j R) *
      bernsteinPolynomial ℂ D j) (D+1)]
    exact (bernstein_reconstruction R D hRdeg).symm
  · intro hdr
    have hzero : R = 0 := by
      dsimp [R]
      rw [truncated_taylor_exact _ _ ((realization_degree d c).trans hdr), sub_self]
    ext j
    simp [hzero, bernsteinCoefficient]

end D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
