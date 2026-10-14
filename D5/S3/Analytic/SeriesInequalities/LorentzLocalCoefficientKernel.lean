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

lemma central_zero (m : ℕ) : centralMoment m 0 = 1 := by
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

lemma tau_degree (m n : ℕ) : (tau m n).natDegree ≤ n := by
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

/-- The exact hypergeometric weight for drawing `n` places from a population
with `J` marked places among `D`. -/
def samplingWeight (D J n h : ℕ) : ℝ :=
  (n.choose h : ℝ) * (J.descFactorial h : ℝ) *
    ((D-J).descFactorial (n-h) : ℝ) / (D.descFactorial n : ℝ)

private lemma sampling_weight_bound {D J n h : ℕ} (hD : 0 < D)
    (hn : 2*n ≤ D) (hJ : J ≤ D) (hh : h ≤ n) :
    samplingWeight D J n h ≤ (2 : ℝ)^n * (n.choose h : ℝ) *
      ((J : ℝ)/D)^h * (1-(J : ℝ)/D)^(n-h) := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hdn : n ≤ D := by omega
  have hden : 0 < (D.descFactorial n : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hdn
  have hlower : ((D : ℝ)/2)^n ≤ (D.descFactorial n : ℝ) := by
    calc
      _ ≤ ((D+1-n : ℕ) : ℝ)^n := by
        apply pow_le_pow_left₀ (by positivity)
        have hsub : ((D+1-n : ℕ) : ℝ) = (D : ℝ)+1-n := by
          rw [Nat.cast_sub (by omega : n ≤ D+1)]; push_cast; ring
        rw [hsub]
        have hnR : 2*(n : ℝ) ≤ D := by exact_mod_cast hn
        linarith
      _ ≤ _ := by exact_mod_cast Nat.pow_sub_le_descFactorial D n
  have hnum1 : (J.descFactorial h : ℝ) ≤ (J : ℝ)^h := by
    exact_mod_cast Nat.descFactorial_le_pow J h
  have hnum2 : ((D-J).descFactorial (n-h) : ℝ) ≤ ((D-J : ℕ) : ℝ)^(n-h) := by
    exact_mod_cast Nat.descFactorial_le_pow (D-J) (n-h)
  unfold samplingWeight
  calc
    _ ≤ ((n.choose h : ℝ) * (J : ℝ)^h * ((D-J : ℕ) : ℝ)^(n-h)) /
        ((D : ℝ)/2)^n := by gcongr
    _ = _ := by
      rw [Nat.cast_sub hJ]
      have hp : 1-(J : ℝ)/D = ((D : ℝ)-J)/D := by field_simp
      rw [hp, div_pow, div_pow, div_pow]
      have he : (D : ℝ)^h * (D : ℝ)^(n-h) = (D : ℝ)^n := by
        rw [← pow_add, Nat.add_sub_of_le hh]
      field_simp
      linear_combination (n.choose h : ℝ) * (J : ℝ)^h * ((D : ℝ)-J)^(n-h) * he

private lemma weighted_power_bound {m : ℕ} (hm : 0 < m)
    {p q δ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hsmall : 1/(m : ℝ) ≤ δ) (hvar : p*q/(m : ℝ) ≤ δ^2)
    (a b : ℕ) (hab : a ≤ b) :
    p^a * q^b * ((m : ℝ)^a / (m : ℝ)^(a+b)) ≤ δ^(a+b) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hqδ : q/(m : ℝ) ≤ δ := (div_le_div_of_nonneg_right hq1 hmR.le).trans hsmall
  have he : p^a * q^b * ((m : ℝ)^a / (m : ℝ)^(a+b)) =
      (p*q/(m : ℝ))^a * (q/(m : ℝ))^(b-a) := by
    have hb : b = a+(b-a) := by omega
    conv_lhs => rw [hb]
    simp only [pow_add, mul_pow, div_pow]
    field_simp
  rw [he]
  calc
    _ ≤ (δ^2)^a * δ^(b-a) := by gcongr
    _ = δ^(a+b) := by rw [← pow_mul, ← pow_add]; congr 1; omega

private lemma weighted_min_bound {m n h : ℕ} (hm : 0 < m) (hh : h ≤ n)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    p^h * (1-p)^(n-h) *
      min ((m : ℝ)^h / (m : ℝ)^n) ((m : ℝ)^(n-h) / (m : ℝ)^n) ≤
        (derivativeRadius m 1 p)^n := by
  have hp0 := hp.1
  have hp1 := hp.2
  let δ := derivativeRadius m 1 p
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hv : 0 ≤ p*(1-p)/(m : ℝ) := by positivity
  have hδ : 0 ≤ δ := le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hsmall : 1/(m : ℝ) ≤ δ := by simpa [δ, derivativeRadius] using
    (le_max_right (Real.sqrt (p*(1-p)/(m : ℝ))) (1/(m : ℝ)))
  have hvar : p*(1-p)/(m : ℝ) ≤ δ^2 := by
    have hs : Real.sqrt (p*(1-p)/(m : ℝ)) ≤ δ := by
      simpa [δ, derivativeRadius] using
        (le_max_left (Real.sqrt (p*(1-p)/(m : ℝ))) (1/(m : ℝ)))
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rwa [Real.sq_sqrt hv] at this
  have hpq : 0 ≤ p^h * (1-p)^(n-h) := by positivity
  rcases le_total h (n-h) with ht | ht
  · refine (mul_le_mul_of_nonneg_left (min_le_left _ _) hpq).trans ?_
    have he : h+(n-h) = n := by omega
    simpa only [he] using weighted_power_bound hm hp.1 (by linarith : 0 ≤ 1-p)
      (by linarith : 1-p ≤ 1) hsmall hvar h (n-h) ht
  · refine (mul_le_mul_of_nonneg_left (min_le_right _ _) hpq).trans ?_
    have he : (n-h)+h = n := by omega
    have hv' : (1-p)*p/(m : ℝ) ≤ δ^2 := by simpa [mul_comm] using hvar
    simpa only [he, mul_comm (p^h) ((1-p)^(n-h))] using
      weighted_power_bound hm (by linarith : 0 ≤ 1-p)
        hp.1 hp.2 hsmall hv' (n-h) h ht

/-- The absolute correction coefficients averaged under the actual sampling
weights obey the endpoint scale, including `J = 0` and `J = D`. -/
theorem weighted_tau_bound (n : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m D J : ℕ, 0 < m → 0 < D → 2*n ≤ D → J ≤ D →
      (∑ h ∈ range (n+1), samplingWeight D J n h *
        ‖bernsteinCoefficient n h (C (((m : ℂ)^n)⁻¹) * tau m n)‖) ≤
          K * (derivativeRadius m 1 ((J : ℝ)/D))^n := by
  obtain ⟨A, hA, hbound⟩ := tau_coefficient_bound n
  let K := (2 : ℝ)^n * A * (2 : ℝ)^n
  have htwo : 1 ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
  refine ⟨K, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le htwo hA) htwo
  intro m D J hm hD hn hJ
  let p : ℝ := (J : ℝ)/D
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hp : p ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hDR).mpr (by exact_mod_cast hJ)
  have hp0 := hp.1
  have hp1 := hp.2
  have hA0 : 0 ≤ A := by linarith
  calc
    _ ≤ ∑ h ∈ range (n+1), (2 : ℝ)^n * A *
        (derivativeRadius m 1 p)^n * (n.choose h : ℝ) := by
      apply sum_le_sum
      intro h hh
      have hhn : h ≤ n := by have := mem_range.mp hh; omega
      have hw := sampling_weight_bound hD hn hJ hhn
      have ht := hbound m hm h hhn
      calc
        _ ≤ ((2 : ℝ)^n * (n.choose h : ℝ) * p^h * (1-p)^(n-h)) *
            (A * min ((m : ℝ)^h/(m : ℝ)^n) ((m : ℝ)^(n-h)/(m : ℝ)^n)) := by
          apply mul_le_mul hw ht (norm_nonneg _)
          positivity
        _ = ((2 : ℝ)^n * A * (n.choose h : ℝ)) *
            (p^h * (1-p)^(n-h) *
              min ((m : ℝ)^h/(m : ℝ)^n) ((m : ℝ)^(n-h)/(m : ℝ)^n)) := by ring
        _ ≤ ((2 : ℝ)^n * A * (n.choose h : ℝ)) * (derivativeRadius m 1 p)^n :=
          mul_le_mul_of_nonneg_left (weighted_min_bound hm hhn hp) (by positivity)
        _ = _ := by ring
    _ = K * (derivativeRadius m 1 p)^n := by
      rw [← mul_sum]
      have hs : (∑ h ∈ range (n+1), (n.choose h : ℝ)) = (2 : ℝ)^n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hs]
      dsimp [K]
      ring

private lemma bernstein_degree {n k : ℕ} (hk : k ≤ n) :
    (bernsteinPolynomial ℂ n k).natDegree ≤ n := by
  have hlin : (1-X : ℂ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  unfold bernsteinPolynomial
  calc
    _ ≤ ((n.choose k : ℂ[X]) * X^k).natDegree + ((1-X : ℂ[X])^ (n-k)).natDegree :=
      natDegree_mul_le
    _ ≤ k + (n-k) := by
      apply Nat.add_le_add
      · exact natDegree_mul_le.trans (by simp)
      · exact (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (n-k) hlin)
    _ = n := Nat.add_sub_of_le hk

private lemma coefficient_basis {D J k : ℕ} (hJ : J ≤ D) (hk : k ≤ D) :
    bernsteinCoefficient D J (bernsteinPolynomial ℂ D k) = if J = k then 1 else 0 := by
  let a : Fin (D+1) → ℂ := fun j => bernsteinCoefficient D j (bernsteinPolynomial ℂ D k)
  let b : Fin (D+1) → ℂ := fun j => if j.val = k then 1 else 0
  have ha : bernsteinRealization D a = bernsteinPolynomial ℂ D k := by
    simp only [bernsteinRealization, a]
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      C (bernsteinCoefficient D j (bernsteinPolynomial ℂ D k)) * bernsteinPolynomial ℂ D j)]
    exact bernstein_reconstruction _ D (bernstein_degree hk)
  have hb : bernsteinRealization D b = bernsteinPolynomial ℂ D k := by
    simp only [bernsteinRealization, b]
    rw [sum_eq_single (⟨k, by omega⟩ : Fin (D+1))]
    · simp
    · intro i _ hi
      have hi' : i.val ≠ k := by intro he; apply hi; exact Fin.ext he
      simp [hi']
    · simp
  exact congrFun (bernstein_representation_unique D a b (ha.trans hb.symm)) ⟨J, by omega⟩

private lemma homogeneous_expansion (a b e : ℕ) :
    (X : ℂ[X])^a * (1-X)^b = ∑ k ∈ range (e+1),
      C ((e.choose k : ℂ) / ((a+b+e).choose (a+k) : ℂ)) *
        bernsteinPolynomial ℂ (a+b+e) (a+k) := by
  have he : (X + (1-X) : ℂ[X])^e = 1 := by simp
  calc
    _ = X^a * (1-X)^b * (X+(1-X))^e := by rw [he, mul_one]
    _ = ∑ k ∈ range (e+1), X^a * (1-X)^b *
        (X^k * (1-X)^(e-k) * (e.choose k : ℂ[X])) := by rw [add_pow, mul_sum]
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ e := by have := mem_range.mp hk; omega
      have hchoose : ((a+b+e).choose (a+k) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega : a+k ≤ a+b+e)).ne'
      have hexp : a+b+e-(a+k) = b+(e-k) := by omega
      simp only [bernsteinPolynomial, hexp, pow_add, ← C_eq_natCast]
      have hc : C ((e.choose k : ℂ) / ((a+b+e).choose (a+k) : ℂ)) *
          C ((a+b+e).choose (a+k) : ℂ) = C (e.choose k : ℂ) := by
        rw [← C_mul, div_mul_cancel₀ _ hchoose]
      linear_combination -(X^a * X^k * (1-X)^b * (1-X)^(e-k)) * hc

private lemma coefficient_homogeneous {D J a b : ℕ} (hJ : J ≤ D) (hab : a+b ≤ D) :
    bernsteinCoefficient D J ((X : ℂ[X])^a * (1-X)^b) =
      if a ≤ J ∧ b ≤ D-J then
        ((D-a-b).choose (J-a) : ℂ) / (D.choose J : ℂ)
      else 0 := by
  have he : a+b+(D-a-b) = D := by omega
  rw [homogeneous_expansion a b (D-a-b)]
  simp only [he, bernsteinCoefficient, finsetSum_coeff, sum_mul, sum_div]
  rw [sum_comm]
  change (∑ k ∈ range (D-a-b+1), bernsteinCoefficient D J
    (C (((D-a-b).choose k : ℂ) / (D.choose (a+k) : ℂ)) * bernsteinPolynomial ℂ D (a+k))) = _
  simp_rw [bernstein_coefficient_C_mul]
  by_cases hvalid : a ≤ J ∧ b ≤ D-J
  · rw [if_pos hvalid]
    rw [sum_eq_single (J-a)]
    · rw [coefficient_basis hJ (by omega), if_pos (by omega : J = a+(J-a)), mul_one]
      rw [show a+(J-a) = J by omega]
    · intro k hk hne
      rw [coefficient_basis hJ (by have := mem_range.mp hk; omega), if_neg (by omega)]
      exact mul_zero _
    · intro hn
      exact (hn (mem_range.mpr (by omega))).elim
  · rw [if_neg hvalid]
    apply sum_eq_zero
    intro k hk
    rw [coefficient_basis hJ (by have := mem_range.mp hk; omega),
      if_neg (by have := mem_range.mp hk; omega), mul_zero]

def homogeneousWeight (D J a b : ℕ) : ℝ :=
  if a ≤ J ∧ b ≤ D-J then ((D-a-b).choose (J-a) : ℝ) / (D.choose J : ℝ) else 0

lemma coefficient_homogeneous_real {D J a b : ℕ} (hJ : J ≤ D) (hab : a+b ≤ D) :
    bernsteinCoefficient D J ((X : ℂ[X])^a * (1-X)^b) =
      (homogeneousWeight D J a b : ℂ) := by
  rw [coefficient_homogeneous hJ hab]
  simp only [homogeneousWeight]
  split_ifs <;> simp

private lemma homogeneous_weight_nonneg (D J a b : ℕ) :
    0 ≤ homogeneousWeight D J a b := by
  unfold homogeneousWeight
  split_ifs <;> positivity

private lemma sampling_weight_identity {D J n h : ℕ} (hn : n ≤ D)
    (hJ : J ≤ D) (hh : h ≤ n) :
    (n.choose h : ℝ) * homogeneousWeight D J h (n-h) = samplingWeight D J n h := by
  unfold homogeneousWeight samplingWeight
  by_cases hvalid : h ≤ J ∧ n-h ≤ D-J
  · rw [if_pos hvalid]
    have hden : (D.descFactorial n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hn).ne'
    have hchoose : (D.choose J : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hJ).ne'
    have h1 : ((D-n).choose (J-h) : ℝ) * ((J-h).factorial : ℝ) *
        ((D-J-(n-h)).factorial : ℝ) = ((D-n).factorial : ℝ) := by
      have he : D-n-(J-h) = D-J-(n-h) := by omega
      exact_mod_cast (he ▸ Nat.choose_mul_factorial_mul_factorial (by omega : J-h ≤ D-n))
    have h2 : ((D-n).factorial : ℝ) * (D.descFactorial n : ℝ) = (D.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hn
    have h3 : ((J-h).factorial : ℝ) * (J.descFactorial h : ℝ) = (J.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hvalid.1
    have h4 : ((D-J-(n-h)).factorial : ℝ) * ((D-J).descFactorial (n-h) : ℝ) =
        ((D-J).factorial : ℝ) := by exact_mod_cast Nat.factorial_mul_descFactorial hvalid.2
    have h5 : (D.choose J : ℝ) * (J.factorial : ℝ) * ((D-J).factorial : ℝ) =
        (D.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hJ
    have hc : ((D-n).choose (J-h) : ℝ) * (D.descFactorial n : ℝ) =
        (D.choose J : ℝ) * (J.descFactorial h : ℝ) * ((D-J).descFactorial (n-h) : ℝ) := by
      apply (mul_right_cancel₀ (show ((J-h).factorial : ℝ) *
        ((D-J-(n-h)).factorial : ℝ) ≠ 0 by positivity))
      calc
        _ = (((D-n).choose (J-h) : ℝ) * ((J-h).factorial : ℝ) *
            ((D-J-(n-h)).factorial : ℝ)) * (D.descFactorial n : ℝ) := by ring
        _ = (D.factorial : ℝ) := by rw [h1, h2]
        _ = (D.choose J : ℝ) * (((J-h).factorial : ℝ) * (J.descFactorial h : ℝ)) *
            (((D-J-(n-h)).factorial : ℝ) * ((D-J).descFactorial (n-h) : ℝ)) := by
          rw [h3, h4, h5]
        _ = _ := by ring
    have he : D-h-(n-h) = D-n := by omega
    rw [he]
    field_simp
    linear_combination (n.choose h : ℝ) * hc
  · rw [if_neg hvalid, mul_zero]
    by_cases hhJ : h ≤ J
    · have hz : (D-J).descFactorial (n-h) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [hz]
    · have hz : J.descFactorial h = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [hz]

private def kernelWeight (D J n h m i : ℕ) : ℝ :=
  (n.choose h : ℝ) * (m.choose i : ℝ) * homogeneousWeight D J (h+i) (n-h+(m-i))

private lemma coefficient_product_basis {D J n h m i : ℕ} (hJ : J ≤ D)
    (hn : n+m ≤ D) (hh : h ≤ n) (hi : i ≤ m) :
    bernsteinCoefficient D J (bernsteinPolynomial ℂ n h * bernsteinPolynomial ℂ m i) =
      (kernelWeight D J n h m i : ℂ) := by
  have he : bernsteinPolynomial ℂ n h * bernsteinPolynomial ℂ m i =
      C ((n.choose h : ℂ) * (m.choose i : ℂ)) *
        (X^(h+i) * (1-X)^(n-h+(m-i))) := by
    simp only [bernsteinPolynomial, map_mul, map_natCast, pow_add]
    ring
  rw [he, bernstein_coefficient_C_mul, coefficient_homogeneous_real hJ (by omega)]
  simp [kernelWeight]

private lemma coefficient_basis_sampling {D J n h : ℕ} (hJ : J ≤ D)
    (hn : n ≤ D) (hh : h ≤ n) :
    bernsteinCoefficient D J (bernsteinPolynomial ℂ n h) = (samplingWeight D J n h : ℂ) := by
  have he : bernsteinPolynomial ℂ n h = C (n.choose h : ℂ) * (X^h*(1-X)^(n-h)) := by
    simp [bernsteinPolynomial, mul_assoc]
  rw [he, bernstein_coefficient_C_mul, coefficient_homogeneous_real hJ (by omega)]
  exact_mod_cast sampling_weight_identity hn hJ hh

private lemma kernel_weight_sum {D J n h m : ℕ} (hJ : J ≤ D) (hn : n+m ≤ D)
    (hh : h ≤ n) :
    (∑ i ∈ range (m+1), kernelWeight D J n h m i) = samplingWeight D J n h := by
  apply Complex.ofReal_injective
  push_cast
  calc
    _ = ∑ i ∈ range (m+1), bernsteinCoefficient D J
        (bernsteinPolynomial ℂ n h * bernsteinPolynomial ℂ m i) := by
      apply sum_congr rfl
      intro i hi
      exact (coefficient_product_basis hJ hn hh (by have := mem_range.mp hi; omega)).symm
    _ = bernsteinCoefficient D J
        (bernsteinPolynomial ℂ n h * ∑ i ∈ range (m+1), bernsteinPolynomial ℂ m i) := by
      rw [mul_sum, bernstein_coefficient_sum]
    _ = _ := by rw [bernsteinPolynomial.sum, mul_one, coefficient_basis_sampling hJ (by omega) hh]

lemma basis_times_local_bound {m r n J h : ℕ} (hn : n ≤ r) (hh : h ≤ n)
    (hJ : J ≤ m+r) (f : ℕ → ℂ) {M : ℝ}
    (hf : ∀ i : ℕ, i ≤ m → i ≤ J → J ≤ i+r → ‖f i‖ ≤ M) :
    ‖bernsteinCoefficient (m+r) J (bernsteinPolynomial ℂ n h *
      ∑ i ∈ range (m+1), C (f i) * bernsteinPolynomial ℂ m i)‖ ≤
        M * samplingWeight (m+r) J n h := by
  rw [mul_sum, bernstein_coefficient_sum]
  calc
    _ ≤ ∑ i ∈ range (m+1), ‖bernsteinCoefficient (m+r) J
        (bernsteinPolynomial ℂ n h * (C (f i) * bernsteinPolynomial ℂ m i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (m+1), M * kernelWeight (m+r) J n h m i := by
      apply sum_le_sum
      intro i hi
      have him : i ≤ m := by have := mem_range.mp hi; omega
      have hk : 0 ≤ kernelWeight (m+r) J n h m i :=
        mul_nonneg (by positivity) (homogeneous_weight_nonneg _ _ _ _)
      rw [mul_left_comm, bernstein_coefficient_C_mul,
        coefficient_product_basis hJ (by omega) hh him, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
      by_cases hlocal : i ≤ J ∧ J ≤ i+r
      · exact mul_le_mul_of_nonneg_right (hf i him hlocal.1 hlocal.2) hk
      · have hzero : kernelWeight (m+r) J n h m i = 0 := by
          unfold kernelWeight homogeneousWeight
          rw [if_neg (by omega)]
          ring
        rw [hzero, mul_zero, mul_zero]
    _ = _ := by rw [← mul_sum, kernel_weight_sum hJ (by omega) hh]

/-- The finite-grid Lorentz polynomial for arbitrary prescribed derivative jets.
For a function, the entry `f ν i` is its `ν`th derivative at `i/m`. -/
def lorentzJet (m r : ℕ) (f : ℕ → ℕ → ℂ) : ℂ[X] :=
  ∑ ν ∈ range (r+1), (C (((m : ℂ)^ν)⁻¹) * tau m ν) *
    ∑ i ∈ range (m+1), C (f ν i) * bernsteinPolynomial ℂ m i

/-- The Lorentz polynomial associated with the actual derivatives of a polynomial. -/
def lorentzOperator (m r : ℕ) (P : ℂ[X]) : ℂ[X] :=
  lorentzJet m r (fun ν i => (derivative^[ν] P).eval ((i : ℂ)/m))

/-- Only the effective local grid entries are required to control a Lorentz
output coefficient. All constants depend on `r` alone. -/
theorem local_coefficient_bound (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, 0 < m → r ≤ m → ∀ J : ℕ, J ≤ m+r →
      ∀ A : ℝ, 0 ≤ A → ∀ f : ℕ → ℕ → ℂ,
      (∀ ν : ℕ, ν ≤ r → ∀ i : ℕ, i ≤ m → i ≤ J → J ≤ i+r →
        ‖f ν i‖ ≤ A / (derivativeRadius m 1 ((J : ℝ)/(m+r)))^ν) →
      ‖bernsteinCoefficient (m+r) J (lorentzJet m r f)‖ ≤ K*A := by
  choose B hB hbound using weighted_tau_bound
  let K := max 1 (∑ ν ∈ range (r+1), B ν)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro m hm hr J hJ A hA f hf
  let δ := derivativeRadius m 1 ((J : ℝ)/(m+r))
  have hδ : 0 < δ := by
    apply lt_of_lt_of_le (show 0 < 1/(m : ℝ) by positivity)
    simpa [δ, derivativeRadius] using
      (le_max_right (Real.sqrt (((J : ℝ)/(m+r))*(1-(J : ℝ)/(m+r))/(m : ℝ))) (1/(m : ℝ)))
  unfold lorentzJet
  rw [bernstein_coefficient_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ ν ∈ range (r+1), B ν * A := by
      apply sum_le_sum
      intro ν hν
      have hνr : ν ≤ r := by have := mem_range.mp hν; omega
      let P := C (((m : ℂ)^ν)⁻¹) * tau m ν
      have hdeg : P.natDegree ≤ ν := (natDegree_C_mul_le _ _).trans (tau_degree m ν)
      have hexp := bernstein_reconstruction P ν hdeg
      change ‖bernsteinCoefficient (m+r) J (P * _)‖ ≤ _
      conv_lhs => rw [← hexp, sum_mul, bernstein_coefficient_sum]
      calc
        _ ≤ ∑ h ∈ range (ν+1), ‖bernsteinCoefficient (m+r) J
            (C (bernsteinCoefficient ν h P) * bernsteinPolynomial ℂ ν h *
              ∑ i ∈ range (m+1), C (f ν i) * bernsteinPolynomial ℂ m i)‖ := norm_sum_le _ _
        _ ≤ ∑ h ∈ range (ν+1), ‖bernsteinCoefficient ν h P‖ *
            ((A/δ^ν) * samplingWeight (m+r) J ν h) := by
          apply sum_le_sum
          intro h hh
          rw [mul_assoc, bernstein_coefficient_C_mul, norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact basis_times_local_bound hνr (by have := mem_range.mp hh; omega) hJ _
            (hf ν hνr)
        _ = (A/δ^ν) * (∑ h ∈ range (ν+1), samplingWeight (m+r) J ν h *
            ‖bernsteinCoefficient ν h P‖) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
        _ ≤ (A/δ^ν) * (B ν * δ^ν) :=
          mul_le_mul_of_nonneg_left (by
            simpa only [P, δ, Nat.cast_add] using hbound ν m (m+r) J hm (by omega) (by omega) hJ)
            (by positivity)
        _ = B ν * A := by field_simp
    _ ≤ K*A := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hA

end D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
