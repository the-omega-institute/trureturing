/- GID: D5/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/LorentzCoefficientRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The coefficient remainder of the actual Lorentz polynomial. -/

import D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel

open Finset Polynomial Complex
open scoped BigOperators
noncomputable section
namespace D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
open LorentzLowDegreeCoefficientRemainder LorentzLocalCoefficientKernel

private lemma tau_convolution (m k : ℕ) :
    (∑ j ∈ range (k+1), C (((j.factorial : ℂ))⁻¹) * centralMoment m j * tau m (k-j)) =
      if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [central_zero, tau]
  | succ n =>
    rw [sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, C_1,
      Nat.sub_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_add_right]
    rw [central_zero, one_mul, tau]
    rw [Fin.sum_univ_eq_sum_range (fun j => C (((j+1).factorial : ℂ)⁻¹) *
      centralMoment m (j+1) * tau m (n-j))]
    ring

private lemma lorentz_sum {ι : Type*} (s : Finset ι) (P : ι → ℂ[X]) (m r : ℕ) :
    lorentzOperator m r (∑ j ∈ s, P j) = ∑ j ∈ s, lorentzOperator m r (P j) := by
  simp only [lorentzOperator, lorentzJet, iterate_derivative_sum, eval_finsetSum,
    map_sum, sum_mul, mul_sum]
  simp_rw [sum_comm (s := range (m+1)) (t := s)]
  rw [sum_comm]

private lemma lorentz_C_mul (m r : ℕ) (a : ℂ) (P : ℂ[X]) :
    lorentzOperator m r (C a * P) = C a * lorentzOperator m r P := by
  simp only [lorentzOperator, lorentzJet, iterate_derivative_C_mul, eval_mul, eval_C,
    map_mul, mul_sum]
  apply sum_congr rfl
  intro ν _
  apply sum_congr rfl
  intro i _
  ring

private lemma lorentz_sub (m r : ℕ) (P Q : ℂ[X]) :
    lorentzOperator m r (P-Q) = lorentzOperator m r P - lorentzOperator m r Q := by
  simp [lorentzOperator, lorentzJet, iterate_derivative_sub, eval_sub, map_sub,
    sub_mul, sum_sub_distrib, mul_sub]

private lemma centered_binomial_eval {m : ℕ} (hm : 0 < m) (j : ℕ) (x : ℂ) :
    (∑ i ∈ range (m+1), ((i : ℂ)/m-x)^j * (bernsteinPolynomial ℂ m i).eval x) =
      (centralMoment m j).eval x / (m : ℂ)^j := by
  have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [centralMoment, eval_finsetSum, eval_mul, eval_pow, eval_sub, eval_C, eval_X, sum_div]
  apply sum_congr rfl
  intro i _
  have he : (i : ℂ)/m-x = ((i : ℂ)-(m : ℂ)*x)/m := by field_simp
  rw [he, div_pow]
  ring

private lemma lorentz_centered_eval {m r k : ℕ} (hm : 0 < m) (hk : k ≤ r) (x : ℂ) :
    (lorentzOperator m r ((X-C x)^k)).eval x = if k = 0 then 1 else 0 := by
  have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [lorentzOperator, lorentzJet, eval_finsetSum, eval_mul, eval_C,
    iterate_derivative_X_sub_pow, eval_smul, nsmul_eq_mul, eval_natCast, eval_pow, eval_sub, eval_X]
  have hinner (ν : ℕ) :
      (∑ i ∈ range (m+1), ((k.descFactorial ν : ℂ) * ((i : ℂ)/m-x)^(k-ν)) *
        (bernsteinPolynomial ℂ m i).eval x) =
          (k.descFactorial ν : ℂ) * ((centralMoment m (k-ν)).eval x / (m : ℂ)^(k-ν)) := by
    rw [← centered_binomial_eval hm]
    rw [mul_sum]
    apply sum_congr rfl
    intros
    ring
  simp_rw [hinner]
  have hsum :
      (∑ ν ∈ range (r+1), ((m : ℂ)^ν)⁻¹ * (tau m ν).eval x *
        ((k.descFactorial ν : ℂ) * ((centralMoment m (k-ν)).eval x / (m : ℂ)^(k-ν)))) =
      ∑ ν ∈ range (k+1), ((m : ℂ)^ν)⁻¹ * (tau m ν).eval x *
        ((k.descFactorial ν : ℂ) * ((centralMoment m (k-ν)).eval x / (m : ℂ)^(k-ν))) := by
    symm
    apply sum_subset (range_mono (by omega))
    intro ν _ hν
    have hz : k.descFactorial ν = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by
      simp only [mem_range, not_lt] at hν; omega)
    simp [hz]
  rw [hsum]
  have he : (∑ ν ∈ range (k+1), ((m : ℂ)^ν)⁻¹ * (tau m ν).eval x *
      ((k.descFactorial ν : ℂ) * ((centralMoment m (k-ν)).eval x / (m : ℂ)^(k-ν)))) =
      (k.factorial : ℂ) / (m : ℂ)^k *
        (∑ ν ∈ range (k+1), ((k-ν).factorial : ℂ)⁻¹ *
          (centralMoment m (k-ν)).eval x * (tau m ν).eval x) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro ν hν
    have hνk : ν ≤ k := by have := mem_range.mp hν; omega
    have hf : ((k-ν).factorial : ℂ) * (k.descFactorial ν : ℂ) = (k.factorial : ℂ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hνk
    have hfac : ((k-ν).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k-ν)
    have hp : (m : ℂ)^ν * (m : ℂ)^(k-ν) = (m : ℂ)^k := by
      rw [← pow_add, Nat.add_sub_of_le hνk]
    field_simp
    linear_combination (tau m ν).eval x * (centralMoment m (k-ν)).eval x * (m : ℂ)^k * hf -
      (tau m ν).eval x * (centralMoment m (k-ν)).eval x * (k.factorial : ℂ) * hp
  rw [he]
  have hc : (∑ ν ∈ range (k+1), ((k-ν).factorial : ℂ)⁻¹ *
      (centralMoment m (k-ν)).eval x * (tau m ν).eval x) =
      if k = 0 then 1 else 0 := by
    have hc := congrArg (fun P : ℂ[X] => P.eval x) (tau_convolution m k)
    simp only [eval_finsetSum, eval_mul, eval_C] at hc
    rw [← sum_range_reflect] at hc
    simp only [Nat.add_sub_cancel] at hc
    convert hc using 1
    · apply sum_congr rfl
      intro ν hν
      rw [Nat.sub_sub_self (by have := mem_range.mp hν; omega)]
    · split_ifs <;> simp
  rw [hc]
  split_ifs with hk0
  · subst k; simp
  · simp

/-- The actual Lorentz operator reproduces every polynomial of degree at most `r`. -/
lemma lorentz_reproduction {m r : ℕ} (hm : 0 < m) (P : ℂ[X])
    (hdeg : P.natDegree ≤ r) : lorentzOperator m r P = P := by
  apply Polynomial.funext
  intro x
  conv_lhs => rw [taylor_expansion_up_to P x hdeg, lorentz_sum]
  simp only [eval_finsetSum, lorentz_C_mul, eval_mul, eval_C]
  have he : (∑ ℓ ∈ range (r+1), (P.taylor x).coeff ℓ *
      (lorentzOperator m r ((X-C x)^ℓ)).eval x) = (P.taylor x).coeff 0 := by
    rw [sum_eq_single 0]
    · rw [lorentz_centered_eval hm (by omega), if_pos rfl, mul_one]
    · intro ℓ hℓ hne
      rw [lorentz_centered_eval hm (by have := mem_range.mp hℓ; omega), if_neg hne, mul_zero]
    · simp
  rw [he, taylor_coeff_zero]

private lemma local_taylor_jet (r ν : ℕ) (hν : ν ≤ r) (P : ℂ[X]) (p h : ℂ)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hP : ∀ z : ℂ, ‖z-p‖ ≤ ρ → ‖P.eval z‖ ≤ M)
    (hh : ‖h‖ ≤ ρ / (2*(2 : ℝ)^r)) :
    ‖(derivative^[ν] (P - truncatedTaylor P p r)).eval (p+h)‖ ≤
      (2*(2 : ℝ)^(r*(r+1))) * M / ρ^(r+1) * ‖h‖^(r+1-ν) := by
  let d := max r P.natDegree
  let q := (2 : ℝ)^r * ‖h‖ / ρ
  have hq0 : 0 ≤ q := by positivity
  have hq : q ≤ 1/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*(2 : ℝ)^r)).mp hh
    dsimp [q]
    apply (div_le_iff₀ hρ).mpr
    nlinarith
  have hc (ℓ : ℕ) : ‖(P.taylor p).coeff ℓ‖ ≤ M / ρ^ℓ := by
    apply coefficient_cauchy_bound _ _ hρ
    intro z hz
    rw [taylor_eval]
    apply hP
    simpa using hz.le
  have hdesc (ℓ : ℕ) : (ℓ.descFactorial ν : ℝ) ≤ (2 : ℝ)^(r*ℓ) := by
    have hl : (ℓ : ℝ) ≤ (2 : ℝ)^ℓ := by exact_mod_cast ℓ.lt_two_pow_self.le
    calc
      _ ≤ (ℓ : ℝ)^ν := by exact_mod_cast Nat.descFactorial_le_pow ℓ ν
      _ ≤ ((2 : ℝ)^ℓ)^ν := pow_le_pow_left₀ (by positivity) hl ν
      _ ≤ ((2 : ℝ)^ℓ)^r := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hν
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  let B := M * (2 : ℝ)^(r*(r+1)) / ρ^(r+1) * ‖h‖^(r+1-ν)
  have hB : 0 ≤ B := by positivity
  rw [taylor_remainder_expansion P p (le_max_right _ _) (le_max_left _ _),
    iterate_derivative_sum, eval_finsetSum]
  calc
    _ ≤ ∑ ℓ ∈ Ico (r+1) (d+1),
        ‖(derivative^[ν] (C ((P.taylor p).coeff ℓ) * (X-C p)^ℓ)).eval (p+h)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ℓ ∈ Ico (r+1) (d+1), B * q^(ℓ-(r+1)) := by
      apply sum_le_sum
      intro ℓ hℓ
      have hrℓ := (mem_Ico.mp hℓ).1
      rw [iterate_derivative_C_mul, iterate_derivative_X_sub_pow]
      simp only [eval_mul, eval_C, eval_smul, nsmul_eq_mul, eval_natCast, eval_pow, eval_sub, eval_X,
        add_sub_cancel_left, norm_mul, Complex.norm_natCast, norm_pow]
      calc
        _ ≤ (M/ρ^ℓ) * ((2 : ℝ)^(r*ℓ) * ‖h‖^(ℓ-ν)) := by gcongr; exact hc ℓ; exact hdesc ℓ
        _ = B * q^(ℓ-(r+1)) := by
          have he : ℓ = (r+1)+(ℓ-(r+1)) := by omega
          have heν : ℓ-ν = (r+1-ν)+(ℓ-(r+1)) := by omega
          rw [heν]
          conv_lhs => rw [he]
          dsimp [B, q]
          simp only [pow_add, Nat.mul_add, mul_pow, div_pow, ← pow_mul, Nat.add_sub_cancel_left]
          field_simp <;> ring
    _ = B * ∑ j ∈ range (d-r), q^j := by
      rw [← mul_sum, sum_Ico_eq_sum_range]
      congr 1
      simp only [Nat.add_sub_add_right, Nat.add_sub_cancel_left]
    _ ≤ B * (1/(1-q)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa [Nat.Ico_zero_eq_range] using
        (geom_sum_Ico_le_of_lt_one (m := 0) (n := d-r) hq0 (by linarith : q < 1))
    _ ≤ B * 2 := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply (div_le_iff₀ (by linarith : 0 < 1-q)).mpr
      linarith
    _ = _ := by dsimp [B]; ring

private lemma radius_scale {d m : ℕ} (hd : 0 < d) (hdm : d ≤ m)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    derivativeRadius m 1 p ≤ Real.sqrt ((d : ℝ)/m) * derivativeRadius d 1 p := by
  have hm : 0 < m := hd.trans_le hdm
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hdmR : (d : ℝ) ≤ m := by exact_mod_cast hdm
  have hp0 := hp.1
  have hp1 := hp.2
  have hρ := (radius_properties hd (by omega : 0 < 1) hp).1
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ)/m)
  have hl : 1/(d : ℝ) ≤ derivativeRadius d 1 p := by
    simpa [derivativeRadius] using
      le_max_right (Real.sqrt (p*(1-p)/(d : ℝ))) (1/(d : ℝ))
  have hv : p*(1-p)/(d : ℝ) ≤ (derivativeRadius d 1 p)^2 := by
    have hb : Real.sqrt (p*(1-p)/(d : ℝ)) ≤ derivativeRadius d 1 p := by
      simpa [derivativeRadius] using
        le_max_left (Real.sqrt (p*(1-p)/(d : ℝ))) (1/(d : ℝ))
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
    rwa [Real.sq_sqrt (by positivity : 0 ≤ p*(1-p)/(d : ℝ))] at this
  rw [show derivativeRadius m 1 p = max (Real.sqrt (p*(1-p)/(m : ℝ))) (1/(m : ℝ)) by
    simp [derivativeRadius]]
  apply max_le
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ p*(1-p)/(m : ℝ)), hs]
    have hmuld := (div_le_iff₀ hdR).mp hv
    rw [div_mul_eq_mul_div]
    simpa [mul_comm] using div_le_div_of_nonneg_right hmuld hmR.le
  · have hr : (d : ℝ)/m ≤ Real.sqrt ((d : ℝ)/m) := by
      have hdiv : (d : ℝ)/m ≤ 1 := (div_le_one hmR).mpr hdmR
      nlinarith [Real.sqrt_nonneg ((d : ℝ)/m), div_nonneg hdR.le hmR.le]
    calc
      1/(m : ℝ) = ((d : ℝ)/m) * (1/(d : ℝ)) := by field_simp
      _ ≤ Real.sqrt ((d : ℝ)/m) * derivativeRadius d 1 p := by gcongr

lemma grid_geometry {m r J i : ℕ} (hm : 0 < m) (hJ : J ≤ m+r)
    (hi : i ≤ m) (hiJ : i ≤ J) (hJi : J ≤ i+r) :
    (i : ℝ)/m ∈ Set.Icc (0 : ℝ) 1 ∧
    (J : ℝ)/(m+r) ∈ Set.Icc (0 : ℝ) 1 ∧
    |(i : ℝ)/m-(J : ℝ)/(m+r)| ≤ (r : ℝ)/m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hD : 0 < (m : ℝ)+r := by positivity
  have hiR : (i : ℝ) ≤ m := by exact_mod_cast hi
  have hJR : (J : ℝ) ≤ (m : ℝ)+r := by exact_mod_cast hJ
  have hiJR : (i : ℝ) ≤ J := by exact_mod_cast hiJ
  have hJiR : (J : ℝ) ≤ (i : ℝ)+r := by exact_mod_cast hJi
  have hp0 : 0 ≤ (J : ℝ)/(m+r) := by positivity
  have hp1 : (J : ℝ)/(m+r) ≤ 1 := (div_le_one hD).mpr hJR
  refine ⟨⟨by positivity, (div_le_one hmR).mpr hiR⟩, ⟨hp0, hp1⟩, ?_⟩
  have he : ((i : ℝ)/m-(J : ℝ)/(m+r)) * m =
      (i : ℝ)-J+((J : ℝ)/(m+r))*r := by field_simp; ring
  rw [abs_le]
  constructor
  · apply (neg_le_iff_add_nonneg).mpr
    have hr : 0 ≤ (r : ℝ) := by positivity
    have hmdiv : (r : ℝ)/m*m = r := div_mul_cancel₀ _ hmR.ne'
    nlinarith [mul_nonneg hp0 hr]
  · apply (le_div_iff₀ hmR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp1 (show 0 ≤ (r : ℝ) by positivity)]

lemma radius_local_comparison {m r : ℕ} (hm : 0 < m) {p t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hdist : |p-t| ≤ (r : ℝ)/m) :
    derivativeRadius m 1 p ≤ ((r : ℝ)+1) * derivativeRadius m 1 t := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hp0 := hp.1
  have hp1 := hp.2
  have ht0 := ht.1
  have ht1 := ht.2
  let δ := derivativeRadius m 1 t
  have hδ := (radius_properties hm (by omega : 0 < 1) ht).1
  have hsmall : 1/(m : ℝ) ≤ δ := by
    simpa [δ, derivativeRadius] using le_max_right (Real.sqrt (t*(1-t)/(m : ℝ))) (1/(m : ℝ))
  have hvar : t*(1-t)/(m : ℝ) ≤ δ^2 := by
    have hh : Real.sqrt (t*(1-t)/(m : ℝ)) ≤ δ := by
      simpa [δ, derivativeRadius] using le_max_left (Real.sqrt (t*(1-t)/(m : ℝ))) (1/(m : ℝ))
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
    rwa [Real.sq_sqrt (by positivity : 0 ≤ t*(1-t)/(m : ℝ))] at this
  have hvdiff : p*(1-p) ≤ t*(1-t)+(r : ℝ)/m := by
    have hb : |1-p-t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have he : p*(1-p)-t*(1-t) = (p-t)*(1-p-t) := by ring
    have hh : p*(1-p)-t*(1-t) ≤ (r : ℝ)/m := by
      calc
        _ ≤ |p*(1-p)-t*(1-t)| := le_abs_self _
        _ = |p-t| * |1-p-t| := by rw [he, abs_mul]
        _ ≤ ((r : ℝ)/m)*1 := mul_le_mul hdist hb (abs_nonneg _) (by positivity)
        _ = _ := mul_one _
    nlinarith
  have hsq : (1/(m : ℝ))^2 ≤ δ^2 := pow_le_pow_left₀ (by positivity) hsmall 2
  have hpvar : p*(1-p)/(m : ℝ) ≤ ((r : ℝ)+1)*δ^2 := by
    have hv := div_le_div_of_nonneg_right hvdiff hmR.le
    have he : (t*(1-t)+(r : ℝ)/m)/(m : ℝ) = t*(1-t)/(m : ℝ)+(r : ℝ)*(1/m)^2 := by ring
    rw [he] at hv
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ (r : ℝ) by positivity)]
  rw [show derivativeRadius m 1 p = max (Real.sqrt (p*(1-p)/(m : ℝ))) (1/(m : ℝ)) by
    simp [derivativeRadius]]
  apply max_le
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ p*(1-p)/(m : ℝ)), mul_pow]
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ)*((r : ℝ)+1) by positivity) (sq_nonneg δ)]
  · exact hsmall.trans (by nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) hδ.le])

private lemma original_derivative_bound {d : ℕ} (hd : 0 < d)
    (c : Fin (d+1) → ℂ) (ν : ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ‖(derivative^[ν] (bernsteinRealization d c)).eval (p : ℂ)‖ ≤
      (ν.factorial : ℝ) * (‖c‖ * Real.exp 6) / (derivativeRadius d 1 p)^ν := by
  have hρ := (radius_properties hd (by omega : 0 < 1) hp).1
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun z : ℂ => (bernsteinRealization d c).eval z) (c := (p : ℂ)) ν hρ
    (bernsteinRealization d c).differentiable.diffContOnCl
    (fun z hz => bernstein_disk_bound hd (by omega : 0 < 1) c
      (fun i => norm_le_pi_norm c i) hp (by simpa [dist_eq_norm] using hz.le))
  rw [polynomial_iterated_deriv] at h
  simpa using h

private lemma original_lorentz_stability (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d m : ℕ, 0 < d → r < d → d ≤ m →
      ∀ c : Fin (d+1) → ℂ, ∀ J : ℕ, J ≤ m+r →
      ‖bernsteinCoefficient (m+r) J (lorentzOperator m r (bernsteinRealization d c))‖ ≤ K*‖c‖ := by
  obtain ⟨L, hL, hlocal⟩ := local_coefficient_bound r
  let A := (r.factorial : ℝ) * Real.exp 6 * ((r : ℝ)+1)^r
  let K := max 1 (L*A)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro d m hd hrd hdm c J hJ
  have hm : 0 < m := hd.trans_le hdm
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h := hlocal m hm (by omega) J hJ (A*‖c‖) (by positivity)
    (fun ν i => (derivative^[ν] (bernsteinRealization d c)).eval ((i : ℂ)/m))
  apply (h ?_).trans
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_right 1 (L*A)) (norm_nonneg c)]
  intro ν hν i hi hiJ hJi
  obtain ⟨ht, hp, hdist⟩ := grid_geometry hm hJ hi hiJ hJi
  let t : ℝ := (i : ℝ)/m
  let p : ℝ := (J : ℝ)/(m+r)
  let ρ := derivativeRadius d 1 t
  let δ := derivativeRadius m 1 p
  have hρ := (radius_properties hd (by omega : 0 < 1) ht).1
  have hδ := (radius_properties hm (by omega : 0 < 1) hp).1
  have hmono : derivativeRadius m 1 t ≤ ρ := by
    apply (radius_scale hd hdm ht).trans
    have hs : Real.sqrt ((d : ℝ)/m) ≤ 1 := (Real.sqrt_le_one).mpr
      ((div_le_one (by exact_mod_cast hm : 0 < (m : ℝ))).mpr (by exact_mod_cast hdm))
    nlinarith
  have hcomp : δ ≤ ((r : ℝ)+1)*ρ :=
    (radius_local_comparison hm hp ht (by simpa [abs_sub_comm] using hdist)).trans
      (mul_le_mul_of_nonneg_left hmono (by positivity))
  have hf : (ν.factorial : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_le hν
  have hpw : ((r : ℝ)+1)^ν ≤ ((r : ℝ)+1)^r := pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) r; linarith) hν
  have hb := original_derivative_bound hd c ν ht
  have hcast : (((i : ℝ)/(m : ℝ) : ℝ) : ℂ) = (i : ℂ)/m := by push_cast; rfl
  rw [hcast] at hb
  apply hb.trans
  apply (div_le_div_iff₀ (pow_pos hρ _) (pow_pos hδ _)).mpr
  have hpow := pow_le_pow_left₀ hδ.le hcomp ν
  rw [mul_pow] at hpow
  have hc : (ν.factorial : ℝ)*((r : ℝ)+1)^ν ≤ (r.factorial : ℝ)*((r : ℝ)+1)^r :=
    mul_le_mul hf hpw (by positivity) (by positivity)
  dsimp [A]
  calc
    _ ≤ ((ν.factorial : ℝ) * (‖c‖ * Real.exp 6)) * (((r : ℝ)+1)^ν*ρ^ν) := by gcongr
    _ ≤ ((r.factorial : ℝ)*((r : ℝ)+1)^r) * (‖c‖*Real.exp 6) * ρ^ν := by
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ (‖c‖*Real.exp 6)*ρ^ν by positivity)]
    _ = _ := by ring

private lemma large_local_remainder (r : ℕ) :
    ∃ A L : ℝ, 1 ≤ A ∧ 1 ≤ L ∧ ∀ d m : ℕ, 0 < d → A*(d : ℝ) ≤ m →
      ∀ c : Fin (d+1) → ℂ, ∀ J : ℕ, J ≤ m+r → ∀ ν : ℕ, ν ≤ r →
      ∀ i : ℕ, i ≤ m → i ≤ J → J ≤ i+r →
      ‖(derivative^[ν] (bernsteinRealization d c -
        truncatedTaylor (bernsteinRealization d c) ((J : ℂ)/(m+r)) r)).eval ((i : ℂ)/m)‖ ≤
          L * ‖c‖ * (Real.sqrt ((d : ℝ)/m))^(r+1) /
            (derivativeRadius m 1 ((J : ℝ)/(m+r)))^ν := by
  let A := max 1 (2*(2 : ℝ)^r*((r : ℝ)+1))
  let G := 2*(2 : ℝ)^(r*(r+1))
  let L := max 1 (G*Real.exp 6*((r : ℝ)+1)^(r+1))
  refine ⟨A, L, le_max_left _ _, le_max_left _ _, ?_⟩
  intro d m hd hAm c J hJ ν hν i hi hiJ hJi
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdmR : (d : ℝ) ≤ m := le_trans (by nlinarith [le_max_left 1 (2*(2 : ℝ)^r*((r : ℝ)+1))]) hAm
  have hdm : d ≤ m := by exact_mod_cast hdmR
  have hm : 0 < m := hd.trans_le hdm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨ht, hp, hdist⟩ := grid_geometry hm hJ hi hiJ hJi
  let p : ℝ := (J : ℝ)/(m+r)
  let t : ℝ := (i : ℝ)/m
  let ρ := derivativeRadius d 1 p
  let δ := derivativeRadius m 1 p
  let H := |t-p|
  have hρ : 0 < ρ := (radius_properties hd (by omega : 0 < 1) hp).1
  have hδ : 0 < δ := (radius_properties hm (by omega : 0 < 1) hp).1
  have hρsmall : 1/(d : ℝ) ≤ ρ := by
    simpa [ρ, derivativeRadius] using le_max_right (Real.sqrt (p*(1-p)/(d : ℝ))) (1/(d : ℝ))
  have hδsmall : 1/(m : ℝ) ≤ δ := by
    simpa [δ, derivativeRadius] using le_max_right (Real.sqrt (p*(1-p)/(m : ℝ))) (1/(m : ℝ))
  have hρd : 1 ≤ ρ*(d : ℝ) := (div_le_iff₀ hdR).mp hρsmall
  have hAd : (2*(2 : ℝ)^r*((r : ℝ)+1))*(d : ℝ) ≤ m :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hdR.le).trans hAm
  have hHsmall : H ≤ ρ/(2*(2 : ℝ)^r) := by
    apply hdist.trans
    apply (div_le_div_iff₀ hmR (by positivity : 0 < 2*(2 : ℝ)^r)).mpr
    have h1 := mul_le_mul_of_nonneg_left hAd hρ.le
    have h2 := mul_le_mul_of_nonneg_left hρd (show 0 ≤ 2*(2 : ℝ)^r*((r : ℝ)+1) by positivity)
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) r]
  have hHδ : H ≤ ((r : ℝ)+1)*δ := by
    apply hdist.trans
    have hh := mul_le_mul_of_nonneg_left hδsmall (show 0 ≤ (r : ℝ) by positivity)
    simp only [mul_one_div] at hh
    nlinarith
  have hscale : δ ≤ Real.sqrt ((d : ℝ)/m)*ρ := radius_scale hd hdm hp
  have hjet := local_taylor_jet r ν hν (bernsteinRealization d c) (p : ℂ)
    ((t : ℂ)-(p : ℂ)) hρ (show 0 ≤ ‖c‖*Real.exp 6 by positivity)
    (fun z hz => by
      simpa using (bernstein_disk_bound hd (by omega : 0 < 1) c
        (fun i => norm_le_pi_norm c i) hp hz))
    (by simpa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hHsmall)
  have hc : (p : ℂ)+((t : ℂ)-(p : ℂ)) = (i : ℂ)/m := by dsimp [t]; push_cast; ring
  rw [hc] at hjet
  have hpcast : (p : ℂ) = (J : ℂ)/(m+r) := by dsimp [p]; push_cast; rfl
  have hn : ‖(t : ℂ)-(p : ℂ)‖ = H := by simp [H, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hn, hpcast] at hjet
  apply hjet.trans
  apply (le_div_iff₀ (pow_pos hδ ν)).mpr
  have hprod : H^(r+1-ν)*δ^ν ≤ ((r : ℝ)+1)^(r+1) *
      (Real.sqrt ((d : ℝ)/m))^(r+1) * ρ^(r+1) := by
    calc
      _ ≤ (((r : ℝ)+1)*δ)^(r+1-ν)*δ^ν := by gcongr
      _ = ((r : ℝ)+1)^(r+1-ν)*δ^(r+1) := by
        rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega : ν ≤ r+1)]
      _ ≤ ((r : ℝ)+1)^(r+1) * (Real.sqrt ((d : ℝ)/m)*ρ)^(r+1) := by
        exact mul_le_mul
          (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
            (Nat.sub_le _ _))
          (pow_le_pow_left₀ hδ.le hscale _) (by positivity) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  calc
    _ = (G*(‖c‖*Real.exp 6)/ρ^(r+1)) * (H^(r+1-ν)*δ^ν) := by dsimp [G]; ring
    _ ≤ (G*(‖c‖*Real.exp 6)/ρ^(r+1)) *
        (((r : ℝ)+1)^(r+1) * (Real.sqrt ((d : ℝ)/m))^(r+1) * ρ^(r+1)) :=
      mul_le_mul_of_nonneg_left hprod (by dsimp [G]; positivity)
    _ = (G*Real.exp 6*((r : ℝ)+1)^(r+1)) * ‖c‖ * (Real.sqrt ((d : ℝ)/m))^(r+1) := by
      field_simp <;> ring
    _ ≤ L*‖c‖*(Real.sqrt ((d : ℝ)/m))^(r+1) := by
      gcongr
      exact le_max_right _ _

lemma original_coefficient_bound {d D J : ℕ} (hdD : d ≤ D) (hJ : J ≤ D)
    (c : Fin (d+1) → ℂ) : ‖bernsteinCoefficient D J (bernsteinRealization d c)‖ ≤ ‖c‖ := by
  let f : ℕ → ℂ := fun i => if hi : i ≤ d then c ⟨i, by omega⟩ else 0
  have h := basis_times_local_bound (m := d) (r := D-d) (n := 0) (h := 0)
    (Nat.zero_le _) (Nat.zero_le _) (by omega : J ≤ d+(D-d)) f
    (fun i hi _ _ => by simp only [f, dif_pos hi]; exact norm_le_pi_norm c _)
  have he : (∑ i ∈ range (d+1), C (f i) * bernsteinPolynomial ℂ d i) = bernsteinRealization d c := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    simp [f, show i.val ≤ d by omega, bernsteinRealization]
  rw [show bernsteinPolynomial ℂ 0 0 = 1 by simp [bernsteinPolynomial], one_mul, he] at h
  simpa [samplingWeight, Nat.add_sub_of_le hdD] using h

lemma coefficient_sub (D J : ℕ) (P Q : ℂ[X]) :
    bernsteinCoefficient D J (P-Q) = bernsteinCoefficient D J P - bernsteinCoefficient D J Q := by
  simp [bernsteinCoefficient, coeff_sub, sub_mul, sub_div, sum_sub_distrib]

private lemma pointwise_remainder_bound (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d m : ℕ, 0 < d → d ≤ m → ∀ c : Fin (d+1) → ℂ,
      ∀ J : ℕ, J ≤ m+r →
      ‖bernsteinCoefficient (m+r) J (bernsteinRealization d c -
        lorentzOperator m r (bernsteinRealization d c))‖ ≤
          K * ((d : ℝ)/m)^(((r : ℝ)+1)/2) * ‖c‖ := by
  obtain ⟨A₁, T, hA₁, hT, htail⟩ := taylor_coefficient_remainder_bound r
  obtain ⟨A₂, L, hA₂, hL, hjet⟩ := large_local_remainder r
  obtain ⟨Q, hQ, hlocal⟩ := local_coefficient_bound r
  obtain ⟨S, hS, hstable⟩ := original_lorentz_stability r
  let A := max A₁ A₂
  let s : ℝ := ((r : ℝ)+1)/2
  let K := max 1 (T+Q*L+(1+S)*A^s)
  have hA : 1 ≤ A := hA₁.trans (le_max_left _ _)
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨K, hK, ?_⟩
  intro d m hd hdm c J hJ
  have hm : 0 < m := hd.trans_le hdm
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hB := norm_nonneg c
  have hKlarge : T+Q*L ≤ K := by
    have hn : 0 ≤ (1+S)*A^s := by positivity
    exact (le_add_of_nonneg_right hn).trans (le_max_right _ _)
  have hKsmall : (1+S)*A^s ≤ K := by
    have hn : 0 ≤ T+Q*L := by positivity
    exact (le_add_of_nonneg_left hn).trans (le_max_right _ _)
  by_cases hdr : d ≤ r
  · rw [lorentz_reproduction hm _ ((realization_degree d c).trans hdr), sub_self]
    simp only [bernsteinCoefficient, coeff_zero, zero_mul, zero_div, sum_const_zero, norm_zero]
    positivity
  have hrd : r < d := by omega
  by_cases hlarge : A*(d : ℝ) ≤ m
  · let P := bernsteinRealization d c
    let p : ℂ := (J : ℂ)/(m+r)
    let R := P-truncatedTaylor P p r
    have hscale : (Real.sqrt ((d : ℝ)/m))^(r+1) = ((d : ℝ)/m)^s := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
      congr 1
      dsimp [s]
      push_cast
      ring
    have hjets (ν : ℕ) (hν : ν ≤ r) (i : ℕ) (hi : i ≤ m) (hiJ : i ≤ J) (hJi : J ≤ i+r) :
        ‖(derivative^[ν] R).eval ((i : ℂ)/m)‖ ≤
          (L*‖c‖*((d : ℝ)/m)^s) / (derivativeRadius m 1 ((J : ℝ)/(m+r)))^ν := by
      have hh := hjet d m hd ((mul_le_mul_of_nonneg_right (le_max_right A₁ A₂) hdR.le).trans hlarge)
        c J hJ ν hν i hi hiJ hJi
      simpa only [R, P, p, hscale] using hh
    have hQR := hlocal m hm (by omega) J hJ (L*‖c‖*((d : ℝ)/m)^s) (by positivity)
      (fun ν i => (derivative^[ν] R).eval ((i : ℂ)/m)) hjets
    have hR := htail d (m+r) hd (by
      have hh := (mul_le_mul_of_nonneg_right (le_max_left A₁ A₂) hdR.le).trans hlarge
      exact hh.trans (by exact_mod_cast Nat.le_add_right m r)) c J hJ
    have hratio : ((d : ℝ)/(m+r : ℕ))^s ≤ ((d : ℝ)/m)^s := by
      apply Real.rpow_le_rpow (by positivity) _ hs
      apply div_le_div_of_nonneg_left hdR.le hmR
      exact_mod_cast Nat.le_add_right m r
    have hR' : ‖bernsteinCoefficient (m+r) J R‖ ≤ T*((d : ℝ)/m)^s*‖c‖ := by
      have hc : (J : ℂ)/(m+r : ℕ) = p := by simp [p]
      rw [hc] at hR
      exact hR.trans (by gcongr)
    have hid : P-lorentzOperator m r P = R-lorentzOperator m r R := by
      dsimp [R]
      rw [lorentz_sub, lorentz_reproduction hm _ (truncated_taylor_degree _ _ _)]
      ring
    change ‖bernsteinCoefficient (m+r) J (P-lorentzOperator m r P)‖ ≤ _
    rw [hid, coefficient_sub]
    calc
      _ ≤ ‖bernsteinCoefficient (m+r) J R‖ +
          ‖bernsteinCoefficient (m+r) J (lorentzOperator m r R)‖ := norm_sub_le _ _
      _ ≤ (T+Q*L)*((d : ℝ)/m)^s*‖c‖ := by
        change ‖bernsteinCoefficient (m+r) J (lorentzOperator m r R)‖ ≤ _ at hQR
        nlinarith [hQR, hR']
      _ ≤ _ := by gcongr
  · have hsmall : 1 ≤ A*((d : ℝ)/m) := by
      have := le_of_lt (lt_of_not_ge hlarge)
      rw [← mul_div_assoc]
      exact (one_le_div hmR).mpr this
    have hp : 1 ≤ A^s*((d : ℝ)/m)^s := by
      rw [← Real.mul_rpow (by linarith : 0 ≤ A) (by positivity)]
      exact Real.one_le_rpow hsmall hs
    have hupper := hstable d m hd hrd hdm c J hJ
    rw [coefficient_sub]
    calc
      _ ≤ ‖bernsteinCoefficient (m+r) J (bernsteinRealization d c)‖ +
          ‖bernsteinCoefficient (m+r) J (lorentzOperator m r (bernsteinRealization d c))‖ := norm_sub_le _ _
      _ ≤ (1+S)*‖c‖ := by
        nlinarith [original_coefficient_bound (hdm.trans (Nat.le_add_right m r)) hJ c]
      _ ≤ ((1+S)*A^s)*((d : ℝ)/m)^s*‖c‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ (1+S)*‖c‖ by positivity)]
      _ ≤ _ := by gcongr

lemma lorentz_degree (m r : ℕ) (f : ℕ → ℕ → ℂ) :
    (lorentzJet m r f).natDegree ≤ m+r := by
  unfold lorentzJet
  apply natDegree_sum_le_of_forall_le
  intro ν hν
  have hνr : ν ≤ r := by have := mem_range.mp hν; omega
  have hgrid : (∑ i ∈ range (m+1), C (f ν i) * bernsteinPolynomial ℂ m i).natDegree ≤ m := by
    have h := realization_degree m (fun i => f ν i)
    simp only [bernsteinRealization] at h
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f ν i) * bernsteinPolynomial ℂ m i)] at h
    exact h
  exact natDegree_mul_le.trans (by
    have hτ := (natDegree_C_mul_le (((m : ℂ)^ν)⁻¹) (tau m ν)).trans (tau_degree m ν)
    omega)

/-- The actual Lorentz remainder has a degree `m+r` Bernstein representation
with a uniform coefficient bound of order `(d/m)^((r+1)/2)`. Its entire array
is zero when `d ≤ r`. The estimate includes all output indices and both endpoints. -/
theorem low_degree_coefficient_remainder (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d m : ℕ, 0 < d → d ≤ m → ∀ c : Fin (d+1) → ℂ,
      ∃ a : Fin (m+r+1) → ℂ,
        bernsteinRealization d c - lorentzOperator m r (bernsteinRealization d c) =
          bernsteinRealization (m+r) a ∧
        ‖a‖ ≤ K * ((d : ℝ)/m)^(((r : ℝ)+1)/2) * ‖c‖ ∧ (d ≤ r → a = 0) := by
  obtain ⟨K, hK, hbound⟩ := pointwise_remainder_bound r
  refine ⟨K, hK, ?_⟩
  intro d m hd hdm c
  let P := bernsteinRealization d c
  let R := P-lorentzOperator m r P
  have hdeg : R.natDegree ≤ m+r := (natDegree_sub_le _ _).trans
    (max_le ((realization_degree d c).trans (hdm.trans (Nat.le_add_right m r))) (lorentz_degree _ _ _))
  refine ⟨fun j => bernsteinCoefficient (m+r) j R, ?_, ?_, ?_⟩
  · unfold bernsteinRealization
    rw [Fin.sum_univ_eq_sum_range (fun j => C (bernsteinCoefficient (m+r) j R) *
      bernsteinPolynomial ℂ (m+r) j)]
    exact (bernstein_reconstruction R (m+r) hdeg).symm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact hbound d m hd hdm c j (by omega)
  · intro hdr
    have hz : R = 0 := by
      dsimp [R]
      rw [lorentz_reproduction (hd.trans_le hdm) P ((realization_degree d c).trans hdr), sub_self]
    ext j
    simp [hz, bernsteinCoefficient]

end D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
