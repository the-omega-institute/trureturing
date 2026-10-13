/- GID: D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual binomial central moments and endpoint bounds for Lorentz corrections. -/

import D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
import D5.S3.Observer.BlockStructure.CommonDenominatorPolynomialBasis

open Finset Polynomial Complex
open scoped BigOperators

noncomputable section
namespace D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel

open LorentzLowDegreeCoefficientRemainder

/-- The actual binomial central moment polynomial, without normalization by `m`. -/
def centralMoment (m j : ℕ) : ℂ[X] :=
  ∑ i ∈ range (m + 1), (C (i : ℂ) - C (m : ℂ) * X) ^ j *
    bernsteinPolynomial ℂ m i

/-- The inverse central-moment correction polynomials in the Lorentz operator. -/
def tau (m : ℕ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => -∑ j : Fin (n + 1),
      C (((j.val + 1).factorial : ℂ)⁻¹) * centralMoment m (j.val + 1) * tau m (n - j.val)
termination_by n => n

private lemma central_zero (m : ℕ) : centralMoment m 0 = 1 := by
  simp [centralMoment, bernsteinPolynomial.sum]

private lemma central_one (m : ℕ) : centralMoment m 1 = 0 := by
  simp only [centralMoment, pow_one, sub_mul, sum_sub_distrib, ← mul_sum]
  have h := bernsteinPolynomial.sum_smul ℂ m
  simp only [nsmul_eq_mul, ← C_eq_natCast] at h
  rw [h, bernsteinPolynomial.sum, mul_one, sub_self]

private lemma bernstein_score (m i : ℕ) (hi : i ≤ m) :
    X * (1 - X) * (bernsteinPolynomial ℂ m i).derivative =
      (C (i : ℂ) - C (m : ℂ) * X) * bernsteinPolynomial ℂ m i := by
  simp only [bernsteinPolynomial, derivative_mul, derivative_pow,
    derivative_natCast, derivative_X, derivative_sub, derivative_one,
    zero_sub, zero_mul, zero_add, mul_one, mul_neg, mul_sub]
  by_cases hi0 : i = 0
  · subst i
    simp only [Nat.sub_zero, pow_zero, mul_one, Nat.choose_zero_right, Nat.cast_one,
      Nat.cast_zero, zero_mul, sub_zero, one_mul, C_0, C_1]
    cases m with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel, pow_succ]; push_cast; ring
  · by_cases hmi : m - i = 0
    · have him : i = m := by omega
      subst i
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.cast_zero, zero_mul, mul_zero,
        sub_zero, Nat.choose_self, Nat.cast_one, one_mul]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      simp only [Nat.add_sub_cancel, pow_succ]
      push_cast
      simp only [map_zero]
      ring
    · have hi' : i - 1 + 1 = i := by omega
      have hm' : m - i - 1 + 1 = m - i := by omega
      have hcast : ((m - i : ℕ) : ℂ) = (m : ℂ) - (i : ℂ) := Nat.cast_sub hi
      have hp : (X : ℂ[X]) ^ i = X ^ (i-1) * X := by rw [← pow_succ, hi']
      have hq : (1-X : ℂ[X]) ^ (m-i) = (1-X) ^ (m-i-1) * (1-X) := by
        rw [← pow_succ, hm']
      rw [hp, hq]
      simp only [← C_eq_natCast, hcast, map_sub]
      ring

private lemma central_recurrence (m j : ℕ) :
    centralMoment m (j + 2) = X * (1-X) *
      (centralMoment m (j+1)).derivative +
      C ((m : ℂ) * (j+1 : ℕ)) * X * (1-X) * centralMoment m j := by
  simp only [centralMoment, derivative_sum, derivative_mul, derivative_pow,
    derivative_sub, derivative_C, derivative_X, zero_mul, zero_add, mul_one,
    zero_sub, mul_neg, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hs := bernstein_score m i (by have := mem_range.mp hi; omega)
  simp only [Nat.add_sub_cancel, pow_succ]
  simp only [map_mul, map_natCast]
  simp only [map_natCast] at hs
  linear_combination -((i : ℂ[X]) - (m : ℂ[X]) * X) ^ (j+1) * hs

private lemma central_degree (m j : ℕ) : (centralMoment m j).natDegree ≤ j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [central_zero]
  | one => simp [central_one]
  | more j hj hj1 =>
    rw [central_recurrence]
    apply natDegree_add_le_of_degree_le
    · calc
        _ ≤ (X * (1-X) : ℂ[X]).natDegree +
            (centralMoment m (j+1)).derivative.natDegree := natDegree_mul_le
        _ ≤ 2 + j := by
          gcongr
          · exact natDegree_mul_le.trans (Nat.add_le_add (show (X : ℂ[X]).natDegree ≤ 1 by simp) (show (1-X : ℂ[X]).natDegree ≤ 1 from (natDegree_sub_le _ _).trans (by simp)))
          · exact (natDegree_derivative_le _).trans (by omega)
        _ = j+2 := by omega
    · calc
        _ ≤ (C ((m : ℂ) * (j+1 : ℕ)) * X * (1-X)).natDegree +
            (centralMoment m j).natDegree := natDegree_mul_le
        _ ≤ 2 + j := by
          gcongr
          exact (natDegree_mul_le.trans (by
            have := natDegree_C_mul_le ((m : ℂ) * (j+1 : ℕ)) (X : ℂ[X])
            have hq := natDegree_sub_le (1 : ℂ[X]) X
            simp only [natDegree_one, natDegree_X, max_eq_right (by omega : 0 ≤ 1)] at hq
            simpa only [natDegree_X] using Nat.add_le_add this hq))
        _ = j+2 := by omega

private lemma central_reflection (m j : ℕ) :
    (centralMoment m j).comp (1-X) = C ((-1 : ℂ)^j) * centralMoment m j := by
  simp only [centralMoment, Polynomial.sum_comp, mul_comp, pow_comp, sub_comp, C_comp, X_comp]
  conv_lhs => rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have him : i ≤ m := by have := mem_range.mp hi; omega
  rw [bernsteinPolynomial.flip ℂ m (m-i) (by omega), Nat.sub_sub_self him]
  have hc : C ((m-i : ℕ) : ℂ) - C (m : ℂ) * (1-X) =
      -(C (i : ℂ) - C (m : ℂ) * X) := by
    rw [Nat.cast_sub him, map_sub]; ring
  rw [hc, neg_pow, C_pow]
  simp only [map_neg, map_one]
  ring

private lemma tau_degree (m n : ℕ) : (tau m n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [tau]
    | succ n =>
      rw [tau, natDegree_neg]
      apply natDegree_sum_le_of_forall_le
      intro j _
      calc
        _ ≤ (C (((j.val+1).factorial : ℂ)⁻¹) * centralMoment m (j.val+1)).natDegree +
            (tau m (n-j.val)).natDegree := natDegree_mul_le
        _ ≤ (j.val+1) + (n-j.val) := by
          gcongr
          · exact (natDegree_mul_le.trans (by simp only [natDegree_C, zero_add]; exact central_degree m _))
          · exact ih _ (by omega)
        _ = n+1 := by omega

private lemma tau_reflection (m n : ℕ) :
    (tau m n).comp (1-X) = C ((-1 : ℂ)^n) * tau m n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [tau]
    | succ n =>
      rw [tau, neg_comp, Polynomial.sum_comp, mul_neg, mul_sum]
      congr 1
      apply sum_congr rfl
      intro j _
      rw [mul_comp, mul_comp, C_comp, central_reflection, ih _ (by omega)]
      have he : (j.val+1) + (n-j.val) = n+1 := by omega
      have hp : C ((-1 : ℂ)^(j.val+1)) * C ((-1 : ℂ)^(n-j.val)) =
          C ((-1 : ℂ)^(n+1)) := by rw [← C_mul, ← pow_add, he]
      linear_combination C (((j.val+1).factorial : ℂ)⁻¹) *
        centralMoment m (j.val+1) * tau m (n-j.val) * hp

private def momentEnvelope (j : ℕ) : ℝ := Real.exp (1 + Real.exp j)

private lemma central_endpoint_disk {m : ℕ} (hm : 0 < m) (j : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 1 / (m : ℝ)) :
    ‖(centralMoment m j).eval z‖ ≤ momentEnvelope j := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmz : (m : ℝ) * ‖z‖ ≤ 1 := by
    have := (le_div_iff₀ hmR).mp hz
    nlinarith
  have hpoint (i : ℕ) : ‖(i : ℂ) - (m : ℂ) * z‖ ≤ i + 1 := by
    calc
      _ ≤ ‖(i : ℂ)‖ + ‖(m : ℂ) * z‖ := norm_sub_le _ _
      _ ≤ i + 1 := by simpa only [Complex.norm_natCast, norm_mul] using add_le_add_right hmz (i : ℝ)
  have hpoly (i : ℕ) : ((i : ℝ) + 1) ^ j ≤ (Real.exp (j : ℝ)) ^ i := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (i : ℝ)+1)
      (Real.add_one_le_exp (i : ℝ)) j
    apply hp.trans_eq
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  have hnorm : ‖1-z‖ ≤ 1+‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
  have hsum : ‖(centralMoment m j).eval z‖ ≤
      ((Real.exp (j : ℝ)) * ‖z‖ + (1 + ‖z‖)) ^ m := by
    simp only [centralMoment, eval_finsetSum]
    refine (norm_sum_le _ _).trans ?_
    rw [add_pow]
    apply sum_le_sum
    intro i hi
    simp only [eval_mul, eval_pow, eval_sub, eval_C, eval_X,
      bernsteinPolynomial, eval_natCast, eval_one, norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (Real.exp (j : ℝ)) ^ i *
          ((m.choose i : ℝ) * ‖z‖ ^ i * (1+‖z‖) ^ (m-i)) := by
        gcongr
        · exact (pow_le_pow_left₀ (norm_nonneg _) (hpoint i) j).trans (hpoly i)
      _ = _ := by rw [mul_pow]; ring
  apply hsum.trans
  have he := Real.add_one_le_exp ((Real.exp (j : ℝ) + 1) * ‖z‖)
  have he' : Real.exp (j : ℝ) * ‖z‖ + (1+‖z‖) ≤
      Real.exp ((Real.exp (j : ℝ) + 1) * ‖z‖) := by nlinarith
  calc
    _ ≤ (Real.exp ((Real.exp (j : ℝ) + 1) * ‖z‖)) ^ m :=
      pow_le_pow_left₀ (by positivity) he' m
    _ = Real.exp ((m : ℝ) * ((Real.exp (j : ℝ) + 1) * ‖z‖)) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ momentEnvelope j := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.exp_pos (j : ℝ)]

private def correctionEnvelope : ℕ → ℝ
  | 0 => 1
  | n+1 => ∑ j : Fin (n+1), momentEnvelope (j.val+1) * correctionEnvelope (n-j.val)
termination_by n => n

private lemma correction_envelope_nonneg (n : ℕ) : 0 ≤ correctionEnvelope n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [correctionEnvelope]
    | succ n =>
      rw [correctionEnvelope]
      exact sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le (ih _ (by omega))

private lemma tau_endpoint_disk {m : ℕ} (hm : 0 < m) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 1 / (m : ℝ)) :
    ‖(tau m n).eval z‖ ≤ correctionEnvelope n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [tau, correctionEnvelope]
    | succ n =>
      rw [tau, eval_neg, norm_neg, eval_finsetSum, correctionEnvelope]
      refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
      simp only [eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_natCast]
      have hf : ((j.val+1).factorial : ℝ)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        exact_mod_cast Nat.factorial_pos (j.val+1)
      calc
        _ ≤ 1 * momentEnvelope (j.val+1) * correctionEnvelope (n-j.val) := by
          exact mul_le_mul (mul_le_mul hf (central_endpoint_disk hm _ hz)
            (norm_nonneg _) (by positivity)) (ih _ (by omega))
            (norm_nonneg _) (by dsimp [momentEnvelope]; positivity)
        _ = _ := by ring

private lemma bernstein_coefficient_left_bound {m n h : ℕ} (hm : 0 < m) (hh : h ≤ n)
    (P : ℂ[X]) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ z : ℂ, ‖z‖ ≤ 1 / (m : ℝ) → ‖P.eval z‖ ≤ M) :
    ‖bernsteinCoefficient n h P‖ ≤ ((n+1 : ℕ) : ℝ) * M * (m : ℝ)^h := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hc (k : ℕ) : ‖P.coeff k‖ ≤ M * (m : ℝ)^k := by
    have hc := coefficient_cauchy_bound P k (by positivity : 0 < 1/(m : ℝ))
      (fun z hz => hP z hz.le)
    simpa [div_pow, div_div] using hc
  unfold bernsteinCoefficient
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ range (n+1), M * (m : ℝ)^h := by
      apply sum_le_sum
      intro k hk
      by_cases hkh : k ≤ h
      · have hcpos : 0 < (n.choose k : ℝ) := by
          exact_mod_cast Nat.choose_pos (hkh.trans hh)
        have hcle : (h.choose k : ℝ) ≤ (n.choose k : ℝ) := by
          exact_mod_cast Nat.choose_le_choose k hh
        simp only [norm_div, norm_mul, Complex.norm_natCast]
        calc
          _ ≤ (M * (m : ℝ)^k) * ((h.choose k : ℝ) / (n.choose k : ℝ)) := by
            rw [mul_div_assoc]; gcongr; exact hc k
          _ ≤ (M * (m : ℝ)^h) * 1 := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hm1 hkh) hM) ((div_le_one hcpos).mpr hcle)
              (by positivity) (by positivity)
          _ = _ := mul_one _
      · simp [Nat.choose_eq_zero_of_lt (by omega : h < k)]
        positivity
    _ = _ := by simp [mul_assoc]

private lemma bernstein_representation_unique (n : ℕ) (a b : Fin (n+1) → ℂ)
    (he : bernsteinRealization n a = bernsteinRealization n b) : a = b := by
  have hlin := D5.S3.Observer.BlockStructure.CommonDenominatorPolynomialBasis.bernstein_linearIndependent_complex n
  funext i
  apply Fintype.linearIndependent_iffₛ.mp hlin a b _ i
  simpa only [bernsteinRealization, smul_eq_C_mul] using he

private lemma bernstein_coefficient_reflection (P : ℂ[X]) (n : ℕ)
    (hdeg : P.natDegree ≤ n) (h : Fin (n+1)) :
    bernsteinCoefficient n h (P.comp (1-X)) = bernsteinCoefficient n (n-h.val) P := by
  have hdeg' : (P.comp (1-X)).natDegree ≤ n := by
    have := natDegree_comp_le (p := P) (q := 1-X)
    have hq : (1-X : ℂ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    exact this.trans ((Nat.mul_le_mul hdeg hq).trans_eq (Nat.mul_one n))
  have he : bernsteinRealization n (fun k => bernsteinCoefficient n k (P.comp (1-X))) =
      bernsteinRealization n (fun k => bernsteinCoefficient n (n-k.val) P) := by
    simp only [bernsteinRealization]
    rw [Fin.sum_univ_eq_sum_range (fun k => C (bernsteinCoefficient n k (P.comp (1-X))) *
      bernsteinPolynomial ℂ n k), bernstein_reconstruction _ _ hdeg']
    conv_lhs => rw [← bernstein_reconstruction P n hdeg, Polynomial.sum_comp]
    rw [Fin.sum_univ_eq_sum_range (fun k => C (bernsteinCoefficient n (n-k) P) *
      bernsteinPolynomial ℂ n k)]
    conv_lhs => rw [← sum_range_reflect]
    simp only [Nat.add_sub_cancel]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by have := mem_range.mp hk; omega
    rw [mul_comp, C_comp, bernsteinPolynomial.flip ℂ n (n-k) (by omega),
      Nat.sub_sub_self hkn]
  exact congrFun (bernstein_representation_unique n _ _ he) h

/-- Every normalized correction coefficient has both endpoint powers, uniformly in
`m`. The correction is defined by the actual binomial central moments. -/
theorem tau_coefficient_bound (n : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, 0 < m → ∀ h : ℕ, h ≤ n →
      ‖bernsteinCoefficient n h (C (((m : ℂ)^n)⁻¹) * tau m n)‖ ≤
        K * min ((m : ℝ)^h / (m : ℝ)^n) ((m : ℝ)^(n-h) / (m : ℝ)^n) := by
  let K := max 1 (((n+1 : ℕ) : ℝ) * correctionEnvelope n)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro m hm h hh
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hK : 0 ≤ K := (zero_le_one.trans (le_max_left _ _))
  have hb (k : ℕ) (hk : k ≤ n) :
      ‖bernsteinCoefficient n k (tau m n)‖ ≤ K * (m : ℝ)^k :=
    (bernstein_coefficient_left_bound hm hk _ (correction_envelope_nonneg n)
      (fun _ hz => tau_endpoint_disk hm n hz)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have href : ‖bernsteinCoefficient n h (tau m n)‖ =
      ‖bernsteinCoefficient n (n-h) (tau m n)‖ := by
    have he := bernstein_coefficient_reflection (tau m n) n (tau_degree m n) ⟨h, by omega⟩
    rw [tau_reflection, bernstein_coefficient_C_mul] at he
    have he' := congrArg norm he
    simpa using he'
  rw [bernstein_coefficient_C_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast,
    mul_min_of_nonneg _ _ hK]
  apply le_min
  · calc
      _ ≤ ((m : ℝ)^n)⁻¹ * (K * (m : ℝ)^h) :=
        mul_le_mul_of_nonneg_left (hb h hh) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ ((m : ℝ)^n)⁻¹ * (K * (m : ℝ)^(n-h)) := by
        rw [href]
        exact mul_le_mul_of_nonneg_left (hb (n-h) (by omega)) (by positivity)
      _ = _ := by ring

end D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
