/- GID: D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted Bernstein derivative kernels on the full closed interval. -/

import D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

open Finset Polynomial Complex
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

/-- The endpoint-adapted Bernstein scale. -/
def delta (n : ℕ) (p : ℝ) : ℝ :=
  max (Real.sqrt (p * (1-p) / n)) (1 / n)

private lemma delta_pos {n : ℕ} (hn : 0 < n) (p : ℝ) : 0 < delta n p :=
  (div_pos zero_lt_one (by exact_mod_cast hn)).trans_le (le_max_right _ _)

private lemma delta_variance {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) : p * (1-p) ≤ n * delta n p ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv : 0 ≤ p * (1-p) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hs := Real.sq_sqrt (div_nonneg hv hnR.le)
  have h := le_max_left (Real.sqrt (p*(1-p)/(n : ℝ))) (1/(n : ℝ))
  have hD := (delta_pos hn p).le
  change Real.sqrt (p*(1-p)/(n : ℝ)) ≤ delta n p at h
  have hsq : p*(1-p)/(n : ℝ) ≤ delta n p ^ 2 := by
    nlinarith [Real.sqrt_nonneg (p*(1-p)/(n : ℝ))]
  exact (div_le_iff₀ hnR).mp hsq |>.trans_eq (mul_comm _ _)

private lemma exp_quadratic {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x^2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at h
  linarith [(abs_le.mp h).2]

private lemma tilted_two_point_bound {p R t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hR : 0 < R) (ht : |t| ≤ 1)
    {z : ℂ} (hz : ‖z - (p : ℂ)‖ ≤ R) :
    Real.exp (t*(1-p)) * ‖z‖ + Real.exp (-t*p) * ‖1-z‖ ≤
      ‖z‖ + ‖1-z‖ + |t| *R + t^2*(p*(1-p)+R) := by
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp.2
  have hq1 : 1-p ≤ 1 := by linarith [hp.1]
  have hza : |‖z‖ - p| ≤ R := by
    have h := abs_norm_sub_norm_le z (p : ℂ)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1] using h.trans hz
  have hzb : |‖1-z‖ - (1-p)| ≤ R := by
    have h := abs_norm_sub_norm_le (1-z) ((1-p : ℝ) : ℂ)
    have he : (1-z) - ((1-p : ℝ) : ℂ) = -(z-(p : ℂ)) := by push_cast; ring
    rw [he, norm_neg] at h
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq] using h.trans hz
  have hlin : |(1-p)*‖z‖ - p*‖1-z‖| ≤ R := by
    calc
      _ = |(1-p)*(‖z‖-p) - p*(‖1-z‖-(1-p))| := by congr 1; ring
      _ ≤ |(1-p)*(‖z‖-p)| + |p*(‖1-z‖-(1-p))| := abs_sub _ _
      _ = (1-p)*|‖z‖-p| + p*|‖1-z‖-(1-p)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp.1, abs_of_nonneg hq]
      _ ≤ (1-p)*R+p*R := add_le_add (mul_le_mul_of_nonneg_left hza hq)
        (mul_le_mul_of_nonneg_left hzb hp.1)
      _ = R := by ring
  have hquad : (1-p)^2*‖z‖ + p^2*‖1-z‖ ≤ p*(1-p)+R := by
    have ha := mul_le_mul_of_nonneg_left (abs_le.mp hza).2 (sq_nonneg (1-p))
    have hb := mul_le_mul_of_nonneg_left (abs_le.mp hzb).2 (sq_nonneg p)
    have hv : 0 ≤ p*(1-p)*R := mul_nonneg (mul_nonneg hp.1 hq) hR.le
    nlinarith
  have he1 := exp_quadratic (x := t*(1-p)) (by
    rw [abs_mul, abs_of_nonneg hq]
    exact (mul_le_mul ht hq1 hq (by norm_num)).trans_eq (one_mul 1))
  have he2 := exp_quadratic (x := -t*p) (by
    rw [abs_mul, abs_neg, abs_of_nonneg hp.1]
    exact (mul_le_mul ht hp.2 hp.1 (by norm_num)).trans_eq (one_mul 1))
  have ha := mul_le_mul_of_nonneg_right he1 (norm_nonneg z)
  have hb := mul_le_mul_of_nonneg_right he2 (norm_nonneg (1-z))
  have hc : t*((1-p)*‖z‖-p*‖1-z‖) ≤ |t| *R :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlin (abs_nonneg t))
  have hd := mul_le_mul_of_nonneg_left hquad (sq_nonneg t)
  nlinarith

private lemma tilted_disk_base {n : ℕ} (hn : 0 < n) {p t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : |t| ≤ 1 / ((n : ℝ) * delta n p))
    {z : ℂ} (hz : ‖z - (p : ℂ)‖ ≤ delta n p) :
    Real.exp (t*(1-p))*‖z‖ + Real.exp (-t*p)*‖1-z‖ ≤ 1+9/(n : ℝ) := by
  let R := delta n p
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hR : 0 < R := delta_pos hn p
  have hsmall : 1/(n : ℝ) ≤ R := le_max_right _ _
  have hnR1 : 1 ≤ (n : ℝ)*R := by
    have := (div_le_iff₀ hnR).mp hsmall
    nlinarith
  have ht1 : |t| ≤ 1 := ht.trans (by
    apply (div_le_iff₀ (mul_pos hnR hR)).mpr
    simpa using hnR1)
  have htr : |t| *R ≤ 1/(n : ℝ) := by
    calc
      _ ≤ (1 / ((n : ℝ)*R))*R := mul_le_mul_of_nonneg_right ht hR.le
      _ = _ := by field_simp
  have hv := delta_variance hn hp
  have hR2 : R ≤ (n : ℝ)*R^2 := by nlinarith
  have hvR : p*(1-p)+R ≤ 2*(n : ℝ)*R^2 := by dsimp [R]; linarith
  have htsq : t^2*R^2 ≤ (1/(n : ℝ))^2 := by
    have := (sq_le_sq₀ (mul_nonneg (abs_nonneg t) hR.le) (by positivity)).mpr htr
    simpa only [mul_pow, sq_abs] using this
  have hquad : t^2*(p*(1-p)+R) ≤ 2/(n : ℝ) := by
    calc
      _ ≤ t^2*(2*(n : ℝ)*R^2) := mul_le_mul_of_nonneg_left hvR (sq_nonneg t)
      _ = 2*(n : ℝ)*(t^2*R^2) := by ring
      _ ≤ 2*(n : ℝ)*(1/(n : ℝ))^2 := mul_le_mul_of_nonneg_left htsq (by positivity)
      _ = _ := by field_simp
  have hradius := (radius_properties hn (by decide : 0 < 1) hp).2
  have heq : derivativeRadius n 1 p = R := by simp [derivativeRadius, R, delta]
  rw [heq, Nat.cast_one] at hradius
  have hgeo := ellipse_disk_bound hp hR hz
  have hsum : ‖z‖+‖1-z‖ ≤ 1+6/(n : ℝ) := by
    rw [mul_div_assoc] at hgeo
    calc
      _ ≤ 1 + 6 * (1/(n : ℝ)) := by linarith
      _ = _ := by ring
  have h := tilted_two_point_bound hp hR ht1 hz
  calc
    _ ≤ ‖z‖ + ‖1-z‖ + |t| * R + t^2*(p*(1-p)+R) := h
    _ ≤ (1+6/(n : ℝ)) + 1/(n : ℝ) + 2/(n : ℝ) := by gcongr
    _ = _ := by ring

private lemma exponential_kernel_identity (n : ℕ) (p t : ℝ) (z : ℂ) :
    (∑ i ∈ range (n+1), Real.exp (t*((i : ℝ)-(n : ℝ)*p)) *
      ‖(bernsteinPolynomial ℂ n i).eval z‖) =
      (Real.exp (t*(1-p))*‖z‖ + Real.exp (-t*p)*‖1-z‖)^n := by
  rw [add_pow]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
    eval_sub, eval_one, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have hexp : Real.exp (t*((i : ℝ)-(n : ℝ)*p)) =
      Real.exp ((i : ℝ)*(t*(1-p))) * Real.exp (((n-i:ℕ):ℝ)*(-t*p)) := by
    rw [← Real.exp_add, Nat.cast_sub hi']
    congr 1
    ring
  rw [hexp]
  ring

/-- Both centered exponential tilts are uniformly bounded on the whole
endpoint-adapted complex disk. -/
private lemma exponential_kernel_disk_bound {n : ℕ} (hn : 0 < n) {p t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : |t| ≤ 1 / ((n : ℝ) * delta n p))
    {z : ℂ} (hz : ‖z - (p : ℂ)‖ ≤ delta n p) :
    (∑ i ∈ range (n+1), Real.exp (t*((i : ℝ)-(n : ℝ)*p)) *
      ‖(bernsteinPolynomial ℂ n i).eval z‖) ≤ Real.exp 9 := by
  rw [exponential_kernel_identity n]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ (1+9/(n : ℝ))^n := pow_le_pow_left₀ (by positivity) (tilted_disk_base hn hp ht hz) n
    _ ≤ (Real.exp (9/(n : ℝ)))^n := pow_le_pow_left₀ (by positivity)
      (by linarith [Real.add_one_le_exp (9/(n : ℝ))]) n
    _ = Real.exp 9 := by rw [← Real.exp_nat_mul]; congr 1; field_simp

private lemma real_power_exponential {γ x : ℝ} (hγ : 0 ≤ γ) (hx : 0 ≤ x) :
    x ^ γ ≤ (1 + (Nat.ceil γ).factorial) * Real.exp x := by
  have hf : 0 ≤ ((Nat.ceil γ).factorial : ℝ) := by positivity
  have he : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 hγ).trans (by nlinarith [Real.exp_pos x])
  · have h := Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge hx1).le (Nat.le_ceil γ)
    rw [Real.rpow_natCast] at h
    have hp := Real.pow_div_factorial_le_exp x hx (Nat.ceil γ)
    have hfpos : 0 < ((Nat.ceil γ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have := (div_le_iff₀ hfpos).mp hp
    nlinarith [Real.exp_pos x]

private lemma weighted_kernel_disk_bound (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 0 < n → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (p : ℂ)‖ ≤ delta n p →
        (∑ i ∈ range (n+1), |(i : ℝ)/(n : ℝ)-p| ^ γ *
          ‖(bernsteinPolynomial ℂ n i).eval z‖) ≤ K * delta n p ^ γ := by
  let A : ℝ := 1 + (Nat.ceil γ).factorial
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2*A*Real.exp 9, by positivity, ?_⟩
  intro n hn p hp z hz
  let R := delta n p
  let t : ℝ := 1 / ((n : ℝ)*R)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hR : 0 < R := delta_pos hn p
  have ht : 0 < t := by dsimp [t]; positivity
  have hplus := exponential_kernel_disk_bound hn hp
    (t := t) (by rw [abs_of_pos ht]) hz
  have hminus := exponential_kernel_disk_bound hn hp
    (t := -t) (by rw [abs_neg, abs_of_pos ht]) hz
  have hpoint (i : ℕ) :
      |(i : ℝ)/(n : ℝ)-p| ^ γ ≤ A*R^γ *
        (Real.exp (t*((i : ℝ)-(n : ℝ)*p)) + Real.exp (-t*((i : ℝ)-(n : ℝ)*p))) := by
    let x : ℝ := (i : ℝ)/(n : ℝ)-p
    have hx : 0 ≤ |x|/R := div_nonneg (abs_nonneg x) hR.le
    have hd := real_power_exponential hγ hx
    have hscale : |x| ^ γ = R^γ * (|x|/R)^γ := by
      rw [Real.div_rpow (abs_nonneg x) hR.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hR γ)]
    have hexp : Real.exp (|x|/R) ≤ Real.exp (x/R) + Real.exp (-x/R) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        linarith [Real.exp_pos (-x/R)]
      · rw [abs_of_nonpos hx, neg_div]
        linarith [Real.exp_pos (x/R)]
    have hreturn : x/R = t*((i : ℝ)-(n : ℝ)*p) := by dsimp [x,t]; field_simp
    calc
      _ = R^γ * (|x|/R)^γ := hscale
      _ ≤ R^γ * (A * Real.exp (|x|/R)) := mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hR.le _)
      _ ≤ R^γ * (A * (Real.exp (x/R) + Real.exp (-x/R))) := by gcongr
      _ = _ := by rw [neg_div, hreturn]; simp only [neg_mul]; ring
  calc
    _ ≤ ∑ i ∈ range (n+1), (A*R^γ *
        (Real.exp (t*((i : ℝ)-(n : ℝ)*p)) + Real.exp (-t*((i : ℝ)-(n : ℝ)*p)))) *
        ‖(bernsteinPolynomial ℂ n i).eval z‖ := by
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hpoint i) (norm_nonneg _)
    _ = A*R^γ * ((∑ i ∈ range (n+1), Real.exp (t*((i : ℝ)-(n : ℝ)*p)) *
        ‖(bernsteinPolynomial ℂ n i).eval z‖) +
        ∑ i ∈ range (n+1), Real.exp (-t*((i : ℝ)-(n : ℝ)*p)) *
        ‖(bernsteinPolynomial ℂ n i).eval z‖) := by
      simp_rw [mul_assoc, add_mul]
      rw [← mul_sum, ← mul_sum, sum_add_distrib]
    _ ≤ A*R^γ * (Real.exp 9 + Real.exp 9) :=
      mul_le_mul_of_nonneg_left (add_le_add hplus hminus) (by positivity)
    _ = _ := by dsimp [R]; ring

private lemma complex_weighted_derivative_kernel (ℓ : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 0 < n → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ range (n+1), |(i : ℝ)/(n : ℝ)-p| ^ γ *
        ‖(derivative^[ℓ] (bernsteinPolynomial ℂ n i)).eval (p : ℂ)‖) ≤
          K * delta n p ^ (γ-(ℓ : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ := weighted_kernel_disk_bound γ hγ
  refine ⟨(ℓ.factorial : ℝ)*K, by positivity, ?_⟩
  intro n hn p hp
  let w : ℕ → ℝ := fun i => |(i : ℝ)/(n : ℝ)-p| ^ γ
  let d : ℕ → ℂ := fun i => (derivative^[ℓ] (bernsteinPolynomial ℂ n i)).eval (p : ℂ)
  let c : ℕ → ℂ := fun i => ((w i * ‖d i‖ : ℝ) : ℂ) / d i
  let P : ℂ[X] := ∑ i ∈ range (n+1), C (c i) * bernsteinPolynomial ℂ n i
  have hw (i : ℕ) : 0 ≤ w i := Real.rpow_nonneg (abs_nonneg _) _
  have hc (i : ℕ) : ‖c i‖ ≤ w i := by
    by_cases hi : d i = 0
    · simp only [c, hi, norm_zero, mul_zero, Complex.ofReal_zero, div_zero, norm_zero]
      exact hw i
    · have hnorm : ‖d i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
      calc
        _ = (w i * ‖d i‖) / ‖d i‖ := by
          simp only [c, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (hw i) (norm_nonneg _))]
        _ = w i := mul_div_cancel_right₀ _ hnorm
        _ ≤ w i := le_rfl
  have hphase (i : ℕ) : c i * d i = ((w i * ‖d i‖ : ℝ):ℂ) := by
    by_cases hi : d i = 0
    · simp [c, hi]
    · exact div_mul_cancel₀ _ hi
  have hPeval : (derivative^[ℓ] P).eval (p : ℂ) =
      ((∑ i ∈ range (n+1), w i * ‖d i‖ : ℝ):ℂ) := by
    simp only [P, iterate_derivative_sum, iterate_derivative_C_mul, eval_finsetSum,
      eval_mul, eval_C]
    push_cast
    exact sum_congr rfl fun i _ => by simpa only [Complex.ofReal_mul] using hphase i
  have hP (z : ℂ) (hz : ‖z - (p : ℂ)‖ ≤ delta n p) :
      ‖P.eval z‖ ≤ K * delta n p ^ γ := by
    calc
      _ ≤ ∑ i ∈ range (n+1), ‖c i‖ * ‖(bernsteinPolynomial ℂ n i).eval z‖ := by
        simpa only [P, eval_finsetSum, eval_mul, eval_C, norm_mul] using
          norm_sum_le (range (n+1)) (fun i => (C (c i) * bernsteinPolynomial ℂ n i).eval z)
      _ ≤ ∑ i ∈ range (n+1), w i * ‖(bernsteinPolynomial ℂ n i).eval z‖ :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
      _ ≤ _ := hbound n hn p hp z hz
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun z : ℂ => P.eval z) (c := (p : ℂ)) ℓ (delta_pos hn p)
    P.differentiable.diffContOnCl (fun z hz => hP z (by
      have hz' : ‖z - (p : ℂ)‖ = delta n p := by
        simpa only [Metric.mem_sphere, dist_eq_norm] using hz
      exact hz'.le))
  simp only [polynomial_iterated_deriv] at h
  rw [hPeval, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _))] at h
  calc
    _ ≤ (ℓ.factorial : ℝ)*(K*delta n p^γ)/delta n p^ℓ := h
    _ = _ := by
      rw [Real.rpow_sub (delta_pos hn p), Real.rpow_natCast]
      ring

/-- Uniform weighted Bernstein derivative bound, including both endpoints,
every nonnegative real exponent and derivative orders above the degree. -/
theorem weighted_derivative_kernel_bound (ℓ : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 0 < n → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ range (n+1), |(i : ℝ)/(n : ℝ)-p| ^ γ *
        |(derivative^[ℓ] (bernsteinPolynomial ℝ n i)).eval p|) ≤
          K * delta n p ^ (γ-(ℓ : ℝ)) := by
  obtain ⟨K,hK,h⟩ := complex_weighted_derivative_kernel ℓ γ hγ
  refine ⟨K,hK,fun n hn p hp => ?_⟩
  have heval (i : ℕ) :
      (derivative^[ℓ] (bernsteinPolynomial ℂ n i)).eval (p : ℂ) =
        (((derivative^[ℓ] (bernsteinPolynomial ℝ n i)).eval p : ℝ):ℂ) := by
    rw [← bernsteinPolynomial.map (Complex.ofRealHom) n i, iterate_derivative_map]
    exact Polynomial.eval_map_apply (p := derivative^[ℓ] (bernsteinPolynomial ℝ n i))
      Complex.ofRealHom p
  simpa only [heval, Complex.norm_real, Real.norm_eq_abs] using h n hn p hp

end D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
