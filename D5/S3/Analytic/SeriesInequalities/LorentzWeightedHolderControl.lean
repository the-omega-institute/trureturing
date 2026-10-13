/- GID: D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted Bernstein kernels and endpoint-uniform Lorentz Hölder control. -/

import D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
Weighted Bernstein derivative estimates and Lorentz approximation in Hölder seminorms.
The estimates include the endpoints and arbitrary nonnegative real kernel weights.
For nonintegral smoothness `β`, take `r < β < r + 1`; no lower derivative sup norms
enter the bounds. The scale is `max (sqrt (p * (1 - p) / n)) (1 / n)`.

The corresponding approximation estimates occur in Holtz, Nazarov and Peres,
*New coins from old, smoothly*, arXiv:0808.1936v3, Lemmas 17 and 19–22.
-/

open Finset Polynomial Complex
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

/-- The endpoint-adapted Bernstein scale. -/
def delta (n : ℕ) (p : ℝ) : ℝ :=
  max (Real.sqrt (p * (1-p) / n)) (1 / n)

lemma delta_pos {n : ℕ} (hn : 0 < n) (p : ℝ) : 0 < delta n p :=
  (div_pos zero_lt_one (by exact_mod_cast hn)).trans_le (le_max_right _ _)

private lemma delta_variance {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) : p * (1 - p) ≤ n * delta n p ^ 2 := by
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
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at h
  linarith [(abs_le.mp h).2]

private lemma tilted_two_point_bound {p R t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hR : 0 < R) (ht : |t| ≤ 1)
    {z : ℂ} (hz : ‖z - (p : ℂ)‖ ≤ R) :
    Real.exp (t * (1 - p)) * ‖z‖ + Real.exp (-t * p) * ‖1 - z‖ ≤
      ‖z‖ + ‖1 - z‖ + |t| * R + t ^ 2 * (p * (1 - p) + R) := by
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
    Real.exp (t * (1 - p)) * ‖z‖ + Real.exp (-t * p) * ‖1 - z‖ ≤ 1 + 9/(n : ℝ) := by
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
    (∑ i ∈ range (n + 1), Real.exp (t * ((i : ℝ) - (n : ℝ) * p)) *
      ‖(bernsteinPolynomial ℂ n i).eval z‖) =
      (Real.exp (t * (1 - p)) * ‖z‖ + Real.exp (-t * p) * ‖1 - z‖) ^ n := by
  rw [add_pow]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X,
    eval_sub, eval_one, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have hexp : Real.exp (t*((i : ℝ)-(n : ℝ)*p)) =
      Real.exp ((i : ℝ)*(t*(1-p))) * Real.exp (((n-i : ℕ) : ℝ)*(-t*p)) := by
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
    (∑ i ∈ range (n + 1), Real.exp (t * ((i : ℝ) - (n : ℝ) * p)) *
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
        (∑ i ∈ range (n + 1), |(i : ℝ)/(n : ℝ) - p| ^ γ *
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
      (∑ i ∈ range (n + 1), |(i : ℝ)/(n : ℝ) - p| ^ γ *
        ‖(derivative^[ℓ] (bernsteinPolynomial ℂ n i)).eval (p : ℂ)‖) ≤
          K * delta n p ^ (γ - (ℓ : ℝ)) := by
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
  have hphase (i : ℕ) : c i * d i = ((w i * ‖d i‖ : ℝ) : ℂ) := by
    by_cases hi : d i = 0
    · simp [c, hi]
    · exact div_mul_cancel₀ _ hi
  have hPeval : (derivative^[ℓ] P).eval (p : ℂ) =
      ((∑ i ∈ range (n+1), w i * ‖d i‖ : ℝ) : ℂ) := by
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
      (∑ i ∈ range (n + 1), |(i : ℝ)/(n : ℝ) - p| ^ γ *
        |(derivative^[ℓ] (bernsteinPolynomial ℝ n i)).eval p|) ≤
          K * delta n p ^ (γ - (ℓ : ℝ)) := by
  obtain ⟨K,hK,h⟩ := complex_weighted_derivative_kernel ℓ γ hγ
  refine ⟨K,hK,fun n hn p hp => ?_⟩
  have heval (i : ℕ) :
      (derivative^[ℓ] (bernsteinPolynomial ℂ n i)).eval (p : ℂ) =
        (((derivative^[ℓ] (bernsteinPolynomial ℝ n i)).eval p : ℝ) : ℂ) := by
    rw [← bernsteinPolynomial.map (Complex.ofRealHom) n i, iterate_derivative_map]
    exact Polynomial.eval_map_apply (p := derivative^[ℓ] (bernsteinPolynomial ℝ n i))
      Complex.ofRealHom p
  simpa only [heval, Complex.norm_real, Real.norm_eq_abs] using h n hn p hp

open LorentzLocalCoefficientKernel

private lemma add_power_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (j : ℕ) :
    (x + y) ^ j ≤ 2 ^ j * (x ^ j + y ^ j) := by
  rcases le_total x y with h | h
  · calc
      _ ≤ (2*y)^j := pow_le_pow_left₀ (by positivity) (by linarith) j
      _ = 2^j*y^j := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg hx j, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
  · calc
      _ ≤ (2*x)^j := pow_le_pow_left₀ (by positivity) (by linarith) j
      _ = 2^j*x^j := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg hy j, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]

private lemma central_moment_disk_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (p : ℂ)‖ ≤ delta m p →
        ‖(centralMoment m j).eval z‖ ≤ K * (m : ℝ) ^ j * delta m p ^ j := by
  obtain ⟨K,hK,h⟩ := weighted_kernel_disk_bound (j : ℝ) (by positivity)
  obtain ⟨B,hB,hb⟩ := weighted_kernel_disk_bound 0 le_rfl
  refine ⟨2^j*(K+B), by positivity, ?_⟩
  intro m hm p hp z hz
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hR := delta_pos hm p
  have hi (i : ℕ) : ‖(i : ℂ)-(m : ℂ)*z‖ ≤
      (m : ℝ)*(|(i : ℝ)/(m : ℝ)-p|+delta m p) := by
    have he : (i : ℂ)-(m : ℂ)*z =
        (m : ℂ)*((((i : ℝ)/(m : ℝ)-p : ℝ) : ℂ)+((p : ℂ)-z)) := by
      push_cast
      field_simp
      ring
    rw [he, norm_mul, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ hmR.le
    calc
      _ ≤ ‖(((i : ℝ)/(m : ℝ)-p : ℝ) : ℂ)‖+‖(p : ℂ)-z‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_sub_rev (p : ℂ) z]
        exact add_le_add le_rfl hz
  have hpoint (i : ℕ) : ‖(i : ℂ)-(m : ℂ)*z‖^j ≤
      (m : ℝ)^j*2^j*(|(i : ℝ)/(m : ℝ)-p|^j+delta m p^j) := by
    calc
      _ ≤ ((m : ℝ)*(|(i : ℝ)/(m : ℝ)-p|+delta m p))^j :=
        pow_le_pow_left₀ (norm_nonneg _) (hi i) j
      _ = (m : ℝ)^j*(|(i : ℝ)/(m : ℝ)-p|+delta m p)^j := mul_pow _ _ _
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (add_power_bound (abs_nonneg _) hR.le j) (pow_nonneg hmR.le j)
  have hj := h m hm p hp z hz
  have hzero := hb m hm p hp z hz
  simp only [Real.rpow_natCast] at hj
  simp only [Real.rpow_zero, one_mul, mul_one] at hzero
  calc
    _ ≤ ∑ i ∈ range (m+1), ‖(i : ℂ)-(m : ℂ)*z‖^j *
        ‖(bernsteinPolynomial ℂ m i).eval z‖ := by
      simp only [centralMoment, eval_finsetSum]
      refine (norm_sum_le _ _).trans_eq ?_
      simp only [eval_mul, eval_pow, eval_sub, eval_C, eval_X, norm_mul, norm_pow]
    _ ≤ ∑ i ∈ range (m+1), ((m : ℝ)^j*2^j*
        (|(i : ℝ)/(m : ℝ)-p|^j+delta m p^j))*‖(bernsteinPolynomial ℂ m i).eval z‖ :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hpoint i) (norm_nonneg _)
    _ = (m : ℝ)^j*2^j*((∑ i ∈ range (m+1), |(i : ℝ)/(m : ℝ)-p|^j *
        ‖(bernsteinPolynomial ℂ m i).eval z‖) +
        delta m p^j * ∑ i ∈ range (m+1), ‖(bernsteinPolynomial ℂ m i).eval z‖) := by
      simp only [mul_sum, mul_add, add_mul, sum_add_distrib]
      congr 1 <;> apply sum_congr rfl <;> intros <;> ring
    _ ≤ (m : ℝ)^j*2^j*(K*delta m p^j+delta m p^j*B) := by gcongr
    _ = _ := by ring

private lemma tau_disk_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (p : ℂ)‖ ≤ delta m p →
        ‖(tau m j).eval z‖ ≤ K * (m : ℝ) ^ j * delta m p ^ j := by
  choose M hM hmoment using central_moment_disk_bound
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => exact ⟨1, by norm_num, fun m hm p hp z hz => by simp [tau]⟩
    | succ j =>
      have hprev (i : Fin (j+1)) := ih (j-i.val) (by omega)
      choose B hB hbound using hprev
      let K := 1+∑ i : Fin (j+1), M (i.val+1)*B i
      have hsum : 0 ≤ ∑ i : Fin (j+1), M (i.val+1)*B i :=
        sum_nonneg fun i _ => (mul_pos (hM _) (hB _)).le
      refine ⟨K, by dsimp [K]; linarith, ?_⟩
      intro m hm p hp z hz
      have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
      have hR := delta_pos hm p
      rw [tau, eval_neg, norm_neg, eval_finsetSum]
      calc
        _ ≤ ∑ i : Fin (j+1),
            ‖(C (((i.val+1).factorial : ℂ)⁻¹)*centralMoment m (i.val+1)*
              tau m (j-i.val)).eval z‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin (j+1), M (i.val+1)*B i*(m : ℝ)^(j+1)*delta m p^(j+1) := by
          apply sum_le_sum
          intro i _
          simp only [eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_natCast]
          have hf : (((i.val+1).factorial : ℝ))⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (i.val+1))
          calc
            _ ≤ 1*(M (i.val+1)*(m : ℝ)^(i.val+1)*delta m p^(i.val+1))*
                (B i*(m : ℝ)^(j-i.val)*delta m p^(j-i.val)) := by
              have hMi := hM (i.val+1)
              exact mul_le_mul (mul_le_mul hf (hmoment _ m hm p hp z hz)
                (norm_nonneg _) (by norm_num)) (hbound i m hm p hp z hz)
                (norm_nonneg _) (by positivity)
            _ = (M (i.val+1)*B i)*((m : ℝ)^(i.val+1)*(m : ℝ)^(j-i.val))*
                (delta m p^(i.val+1)*delta m p^(j-i.val)) := by ring
            _ = _ := by rw [← pow_add, ← pow_add, show i.val+1+(j-i.val)=j+1 by omega]
        _ = (∑ i : Fin (j+1), M (i.val+1)*B i)*(m : ℝ)^(j+1)*delta m p^(j+1) := by
          rw [sum_mul, sum_mul]
        _ ≤ _ := by dsimp [K]; gcongr; linarith

private lemma lorentz_jet_derivative_bound (r ℓ : ℕ) (β : ℝ) (hβ : (r : ℝ) ≤ β) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      ∀ A : ℝ, 0 ≤ A → ∀ f : ℕ → ℕ → ℂ,
      (∀ ν ≤ r, ∀ i ≤ m, ‖f ν i‖ ≤ A * |(i : ℝ)/(m : ℝ) - p| ^ (β - (ν : ℝ))) →
      ‖(derivative^[ℓ] (lorentzJet m r f)).eval (p : ℂ)‖ ≤ K * A * delta m p ^ (β - (ℓ : ℝ)) := by
  choose T hT htau using tau_disk_bound
  choose W hW hweight using fun γ : ℝ => weighted_kernel_disk_bound |γ| (abs_nonneg γ)
  let B := 1 + ∑ ν ∈ range (r+1), T ν * W (β-(ν : ℝ))
  have hB : 0 < B := by
    have := sum_nonneg (s := range (r+1)) (fun ν _ => (mul_pos (hT ν) (hW (β-(ν : ℝ)))).le)
    dsimp [B]
    linarith
  refine ⟨(ℓ.factorial : ℝ)*B, by positivity, ?_⟩
  intro m hm p hp A hA f hf
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hR := delta_pos hm p
  have hQ (z : ℂ) (hz : ‖z-(p : ℂ)‖ ≤ delta m p) :
      ‖(lorentzJet m r f).eval z‖ ≤ B*A*delta m p^β := by
    have hterm (ν : ℕ) (hν : ν ∈ range (r+1)) :
        ‖((C (((m : ℂ)^ν)⁻¹) * tau m ν) *
          ∑ i ∈ range (m+1), C (f ν i)*bernsteinPolynomial ℂ m i).eval z‖ ≤
            (T ν * W (β-(ν : ℝ)))*A*delta m p^β := by
      have hνr : ν ≤ r := Nat.le_of_lt_succ (mem_range.mp hν)
      have hβν : 0 ≤ β-(ν : ℝ) := by
        have : (ν : ℝ) ≤ r := by exact_mod_cast hνr
        linarith
      have hw := hweight (β-(ν : ℝ)) m hm p hp z hz
      rw [abs_of_nonneg hβν] at hw
      have hi : ‖(∑ i ∈ range (m+1), C (f ν i)*bernsteinPolynomial ℂ m i).eval z‖ ≤
          A * (W (β-(ν : ℝ))*delta m p^(β-(ν : ℝ))) := by
        calc
          _ ≤ ∑ i ∈ range (m+1), ‖f ν i‖*‖(bernsteinPolynomial ℂ m i).eval z‖ := by
            simpa only [eval_finsetSum, eval_mul, eval_C, norm_mul] using
              norm_sum_le (range (m+1)) (fun i => (C (f ν i)*bernsteinPolynomial ℂ m i).eval z)
          _ ≤ ∑ i ∈ range (m+1), (A*|(i : ℝ)/(m : ℝ)-p|^(β-(ν : ℝ)))*
              ‖(bernsteinPolynomial ℂ m i).eval z‖ := by
            exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
              (hf ν hνr i (Nat.le_of_lt_succ (mem_range.mp hi))) (norm_nonneg _)
          _ = A * ∑ i ∈ range (m+1), |(i : ℝ)/(m : ℝ)-p|^(β-(ν : ℝ))*
              ‖(bernsteinPolynomial ℂ m i).eval z‖ := by simp_rw [mul_assoc]; rw [mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left hw hA
      simp only [eval_mul, eval_C, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      calc
        _ ≤ ((m : ℝ)^ν)⁻¹ * (T ν*(m : ℝ)^ν*delta m p^ν) *
            (A*(W (β-(ν : ℝ))*delta m p^(β-(ν : ℝ)))) := by
          have hTν := hT ν
          exact mul_le_mul (mul_le_mul_of_nonneg_left (htau ν m hm p hp z hz)
            (by positivity)) hi (norm_nonneg _) (by positivity)
        _ = (T ν*W (β-(ν : ℝ)))*A*(delta m p^(ν : ℝ)*delta m p^(β-(ν : ℝ))) := by
          rw [Real.rpow_natCast]
          field_simp
        _ = _ := by rw [← Real.rpow_add hR]; congr 2; ring
    calc
      _ ≤ ∑ ν ∈ range (r+1), ‖((C (((m : ℂ)^ν)⁻¹)*tau m ν)*
          ∑ i ∈ range (m+1), C (f ν i)*bernsteinPolynomial ℂ m i).eval z‖ := by
        simpa only [lorentzJet, eval_finsetSum] using norm_sum_le (range (r+1))
          (fun ν => ((C (((m : ℂ)^ν)⁻¹)*tau m ν)*
            ∑ i ∈ range (m+1), C (f ν i)*bernsteinPolynomial ℂ m i).eval z)
      _ ≤ ∑ ν ∈ range (r+1), (T ν*W (β-(ν : ℝ)))*A*delta m p^β := sum_le_sum hterm
      _ = (∑ ν ∈ range (r+1), T ν*W (β-(ν : ℝ)))*A*delta m p^β := by
        rw [sum_mul, sum_mul]
      _ ≤ _ := by dsimp [B]; gcongr; linarith
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun z : ℂ => (lorentzJet m r f).eval z) (c := (p : ℂ)) ℓ hR
    (lorentzJet m r f).differentiable.diffContOnCl (fun z hz => hQ z (by
      have hz' : ‖z-(p : ℂ)‖ = delta m p := by
        simpa only [Metric.mem_sphere, dist_eq_norm] using hz
      exact hz'.le))
  simp only [polynomial_iterated_deriv] at hc
  calc
    _ ≤ (ℓ.factorial : ℝ)*(B*A*delta m p^β)/delta m p^ℓ := hc
    _ = _ := by rw [Real.rpow_sub hR, Real.rpow_natCast]; ring

private lemma exists_taylor_jet (r : ℕ) (p : ℂ) (a : ℕ → ℂ) :
    ∃ P : ℂ[X], P.natDegree ≤ r ∧ ∀ j ≤ r, (derivative^[j] P).eval p = a j := by
  let P : ℂ[X] := ∑ k ∈ range (r+1), C (a k / (k.factorial : ℂ)) * (X+C (-p))^k
  refine ⟨P, ?_, ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le k
      (le_of_eq (natDegree_X_add_C (-p)))).trans (by have := mem_range.mp hk; omega))
  · intro j hj
    simp only [P, iterate_derivative_sum, iterate_derivative_C_mul,
      iterate_derivative_X_add_pow, eval_finsetSum, eval_mul, eval_C,
      eval_pow, eval_add, eval_X, add_neg_cancel, nsmul_eq_mul]
    rw [sum_eq_single j]
    · simp only [Nat.sub_self, pow_zero, mul_one, Nat.descFactorial_self, eval_natCast]
      exact div_mul_cancel₀ (a j)
        (show (j.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero j)
    · intro k hk hkj
      rcases lt_or_gt_of_ne hkj with h | h
      · simp [Nat.descFactorial_of_lt h]
      · simp [zero_pow (Nat.sub_ne_zero_of_lt h)]
    · intro hjmem
      exact (hjmem (mem_range.mpr (by omega))).elim

private lemma vanishing_jet_bound {r : ℕ} {β A p : ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hβ : (r : ℝ) ≤ β)
    (hA : 0 ≤ A) (hp : p ∈ s) (g : ℕ → ℝ → ℂ)
    (hd : ∀ j < r, ∀ x ∈ s, HasDerivWithinAt (g j) (g (j + 1) x) s x)
    (hz : ∀ j < r, g j p = 0)
    (htop : ∀ x ∈ s, ‖g r x‖ ≤ A * |x - p| ^ (β - (r : ℝ))) :
    ∀ j ≤ r, ∀ x ∈ s, ‖g j x‖ ≤ A * |x - p| ^ (β - (j : ℝ)) := by
  intro j hj
  induction hj using Nat.decreasingInduction with
  | self => exact htop
  | @of_succ j hj ih =>
    intro x hx
    have hsub : Set.uIcc p x ⊆ s := hs.ordConnected.uIcc_subset hp hx
    have hexp : 0 ≤ β-((j+1 : ℕ) : ℝ) := by
      have : ((j+1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hj
      linarith
    have hb (y : ℝ) (hy : y ∈ Set.uIcc p x) :
        ‖g (j+1) y‖ ≤ A*|x-p|^(β-((j+1 : ℕ) : ℝ)) := by
      exact (ih y (hsub hy)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (Set.abs_sub_left_of_mem_uIcc hy) hexp) hA)
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hd j (by omega) y (hsub hy)).mono hsub) hb
      (convex_uIcc p x) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
    rw [hz j (by omega), sub_zero, Real.norm_eq_abs] at h
    calc
      _ ≤ (A*|x-p|^(β-((j+1 : ℕ) : ℝ)))*|x-p| := h
      _ = A*|x-p|^(β-(j : ℝ)) := by
        have he : β-(j : ℝ) = (β-((j+1 : ℕ) : ℝ)) + 1 := by push_cast; ring
        rw [he, Real.rpow_add_of_nonneg (abs_nonneg _) hexp (by norm_num), Real.rpow_one]
        ring

private lemma holder_taylor_remainder {r : ℕ} {β A p : ℝ} (hβ : (r : ℝ) ≤ β)
    (hA : 0 ≤ A) (hp : p ∈ Set.Icc (0 : ℝ) 1) (f : ℕ → ℝ → ℂ)
    (hd : ∀ j < r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (f j) (f (j + 1) x) (Set.Icc 0 1) x)
    (hh : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f r x - f r p‖ ≤ A * |x - p| ^ (β - (r : ℝ))) :
    ∃ P : ℂ[X], P.natDegree ≤ r ∧
      (∀ j ≤ r, (derivative^[j] P).eval (p : ℂ) = f j p) ∧
      ∀ j ≤ r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖f j x - (derivative^[j] P).eval (x : ℂ)‖ ≤ A * |x - p| ^ (β - (j : ℝ)) := by
  obtain ⟨P,hdeg,hP⟩ := exists_taylor_jet r (p : ℂ) (fun j => f j p)
  refine ⟨P,hdeg,hP,?_⟩
  let g : ℕ → ℝ → ℂ := fun j x => f j x-(derivative^[j] P).eval (x : ℂ)
  have hg (j : ℕ) (hj : j < r) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt (g j) (g (j+1) x) (Set.Icc 0 1) x := by
    have hpoly := ((derivative^[j] P).hasDerivAt (x : ℂ)).comp_ofReal
    convert! (hd j hj x hx).sub hpoly.hasDerivWithinAt using 1
    simp only [g, Function.iterate_succ_apply']
  have hzero (j : ℕ) (hj : j < r) : g j p = 0 := by simp [g,hP j hj.le]
  have hconst : ∀ x : ℝ, (derivative^[r] P).eval (x : ℂ) = f r p := by
    have hz : (derivative^[r] P).natDegree = 0 := by
      have := natDegree_iterate_derivative P r
      omega
    have he := hP r le_rfl
    rw [eq_C_of_natDegree_eq_zero hz, eval_C] at he
    intro x
    rw [eq_C_of_natDegree_eq_zero hz, eval_C]
    exact he
  exact vanishing_jet_bound (convex_Icc 0 1) hβ hA hp g hg hzero
    (fun x hx => by simpa only [g,hconst] using hh x hx)

private lemma lorentz_jet_sub_polynomial {m r : ℕ} (hm : 0 < m)
    (f : ℕ → ℝ → ℂ) (P : ℂ[X]) (hP : P.natDegree ≤ r) :
    lorentzJet m r (fun j i => f j ((i : ℝ)/(m : ℝ))-
      (derivative^[j] P).eval (((i : ℝ)/(m : ℝ) : ℝ) : ℂ)) =
      lorentzJet m r (fun j i => f j ((i : ℝ)/(m : ℝ))) - P := by
  conv_rhs => rw [← LorentzCoefficientRemainder.lorentz_reproduction hm P hP]
  simp only [lorentzOperator, lorentzJet, map_sub, sub_mul, mul_sub,
    sum_sub_distrib, Complex.ofReal_div, Complex.ofReal_natCast]

/-- The actual finite Lorentz operator on the interval derivatives of a function. -/
def holderOperator (m r : ℕ) (f : ℝ → ℂ) : ℂ[X] :=
  lorentzJet m r (fun j i => iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) ((i : ℝ)/(m : ℝ)))

/-- Simultaneous approximation and the next derivative are controlled by the
top derivative's Hölder seminorm, without lower-derivative sup norms. -/
theorem holder_derivative_control (r : ℕ) (β : ℝ) (hβ : (r : ℝ) < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℂ), ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) y‖ ≤ A * |x - y| ^ (β - (r : ℝ))) →
      ∀ m : ℕ, 0 < m → ∀ p ∈ Set.Icc (0 : ℝ) 1,
        (∀ j ≤ r, ‖iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) p -
          (derivative^[j] (holderOperator m r f)).eval (p : ℂ)‖ ≤
            K * A * delta m p ^ (β - (j : ℝ))) ∧
        ‖(derivative^[r + 1] (holderOperator m r f)).eval (p : ℂ)‖ ≤
          K * A * delta m p ^ (β - ((r + 1 : ℕ) : ℝ)) := by
  choose C hC hbound using fun j : ℕ => lorentz_jet_derivative_bound r j β hβ.le
  let K := 1+∑ j ∈ range (r+2), C j
  have hK : 0 < K := by
    have := sum_nonneg (s := range (r+2)) (fun j _ => (hC j).le)
    dsimp [K]
    linarith
  have hCk (j : ℕ) (hj : j ≤ r+1) : C j ≤ K := by
    have := single_le_sum (s := range (r+2)) (f := C)
      (fun i _ => (hC i).le) (mem_range.mpr (by omega : j < r+2))
    dsimp [K]
    linarith
  refine ⟨K,hK,?_⟩
  intro f hf A hA hh m hm p hp
  let F : ℕ → ℝ → ℂ := fun j => iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1)
  have hd (j : ℕ) (hj : j < r) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt (F j) (F (j+1) x) (Set.Icc 0 1) x := by
    dsimp [F]
    rw [iteratedDerivWithin_succ]
    exact (hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj)
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) x hx).hasDerivWithinAt
  obtain ⟨P,hdeg,hP,hrem⟩ := holder_taylor_remainder hβ.le hA hp F hd (fun x hx => hh x hx p hp)
  let g : ℕ → ℕ → ℂ := fun j i => F j ((i : ℝ)/(m : ℝ))-
    (derivative^[j] P).eval (((i : ℝ)/(m : ℝ) : ℝ) : ℂ)
  have hg (j : ℕ) (hj : j ≤ r) (i : ℕ) (hi : i ≤ m) :
      ‖g j i‖ ≤ A*|(i : ℝ)/(m : ℝ)-p|^(β-(j : ℝ)) := by
    apply hrem j hj _
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hm : (0 : ℝ)<m)).mpr
      exact_mod_cast hi
  have hdiff : lorentzJet m r g = holderOperator m r f-P :=
    lorentz_jet_sub_polynomial hm F P hdeg
  have hb (j : ℕ) (hj : j ≤ r+1) :
      ‖(derivative^[j] (holderOperator m r f-P)).eval (p : ℂ)‖ ≤ K*A*delta m p^(β-(j : ℝ)) := by
    rw [← hdiff]
    exact (hbound j m hm p hp A hA g hg).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCk j hj) hA)
        (Real.rpow_nonneg (delta_pos hm p).le _))
  constructor
  · intro j hj
    have h := hb j (by omega)
    rw [iterate_derivative_sub, eval_sub, hP j hj, norm_sub_rev] at h
    exact h
  · have h := hb (r+1) le_rfl
    rw [iterate_derivative_sub, iterate_derivative_eq_zero (by omega : P.natDegree < r+1),
      sub_zero] at h
    exact h

private lemma delta_square_comparison {m : ℕ} (hm : 0 < m) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    delta m x ^ 2 ≤ delta m y ^ 2 + |x - y|/(m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hv : x*(1-x) ≤ y*(1-y)+|x-y| := by
    have hlin : |1-x-y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
    have h := mul_le_mul_of_nonneg_left hlin (abs_nonneg (x-y))
    rw [← abs_mul] at h
    have he : (x-y)*(1-x-y)=x*(1-x)-y*(1-y) := by ring
    rw [he,mul_one] at h
    linarith [(abs_le.mp h).2]
  have hyinv : 1/(m : ℝ) ≤ delta m y := le_max_right _ _
  have hyv := delta_variance hm hy
  have hys := delta_pos hm y
  have hxs : 0 ≤ x*(1-x)/(m : ℝ) := div_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) hmR.le
  change (max (Real.sqrt (x*(1-x)/(m : ℝ))) (1/(m : ℝ)))^2 ≤ _
  rcases le_total (Real.sqrt (x*(1-x)/(m : ℝ))) (1/(m : ℝ)) with h | h
  · rw [max_eq_right h]
    have hinv : 0 ≤ 1/(m : ℝ) := by positivity
    nlinarith [div_nonneg (abs_nonneg (x-y)) hmR.le]
  · rw [max_eq_left h,Real.sq_sqrt hxs]
    apply (div_le_iff₀ hmR).mpr
    have hc : (|x-y|/(m : ℝ))*(m : ℝ)=|x-y| := div_mul_cancel₀ _ hmR.ne'
    nlinarith

lemma inverse_delta_comparison {m : ℕ} (hm : 0 < m) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    delta m x / delta m y ≤ 1 + |x - y|/delta m x := by
  have hs := delta_square_comparison hm hx hy
  have hxp := delta_pos hm x
  have hyp := delta_pos hm y
  have hyinv : 1/(m : ℝ) ≤ delta m y := le_max_right _ _
  have hd := mul_le_mul_of_nonneg_right hyinv (abs_nonneg (x-y))
  rw [div_mul_eq_mul_div,one_mul] at hd
  have hprod : delta m x^2 ≤ delta m y*(delta m x+|x-y|) := by
    rcases le_total (delta m y) (delta m x) with h | h
    · nlinarith [mul_nonneg hyp.le (sub_nonneg.mpr h)]
    · nlinarith [mul_nonneg hxp.le (sub_nonneg.mpr h),
        mul_nonneg hyp.le (abs_nonneg (x-y))]
  apply (div_le_iff₀ hyp).mpr
  apply (mul_le_mul_iff_left₀ hxp).mp
  have he : ((1+|x-y|/delta m x)*delta m y)*delta m x=
      delta m y*(delta m x+|x-y|) := by field_simp
  rw [he]
  nlinarith

private lemma negative_delta_comparison {m : ℕ} (hm : 0 < m) {x y e : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (he : 0 ≤ e) (he1 : e ≤ 1) :
    delta m y ^ (-e) ≤ delta m x ^ (-e) * (1 + |x - y|/delta m x) := by
  have hxp := delta_pos hm x
  have hyp := delta_pos hm y
  have hq : 1 ≤ 1+|x-y|/delta m x := by
    have : 0 ≤ |x-y|/delta m x := by positivity
    linarith
  have hb := (Real.rpow_le_rpow (by positivity : 0 ≤ delta m x/delta m y)
    (inverse_delta_comparison hm hx hy) he).trans
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq he1)
  calc
    _ = delta m x^(-e)*(delta m x/delta m y)^e := by
      rw [Real.div_rpow hxp.le hyp.le, Real.rpow_neg hxp.le, Real.rpow_neg hyp.le]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hxp.le _)

/-- The Lorentz operator preserves the top Hölder seminorm uniformly in its
grid degree. This is a seminorm statement, not a bound on a full norm. -/
theorem holder_seminorm_control (r : ℕ) (β : ℝ) (hβ : (r : ℝ) < β)
    (hβ1 : β < (r : ℝ) + 1) :
    ∃ L : ℝ, 0 < L ∧ ∀ (f : ℝ → ℂ), ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) y‖ ≤ A * |x - y| ^ (β - (r : ℝ))) →
      ∀ m : ℕ, 0 < m → ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖(derivative^[r] (holderOperator m r f)).eval (x : ℂ) -
          (derivative^[r] (holderOperator m r f)).eval (y : ℂ)‖ ≤
            L * A * |x - y| ^ (β - (r : ℝ)) := by
  obtain ⟨K,hK,h⟩ := holder_derivative_control r β hβ
  refine ⟨2*K+1,by positivity,?_⟩
  intro f hf A hA hh m hm
  let Q := holderOperator m r f
  let F := iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1)
  let θ := β-(r : ℝ)
  let e := (r : ℝ)+1-β
  have he : 0 ≤ e := by dsimp [e]; linarith
  have he1 : e ≤ 1 := by dsimp [e]; linarith
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have hhigh (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      ‖(derivative^[r+1] Q).eval (z : ℂ)‖ ≤ K*A*delta m z^(-e) := by
    have heq : β-((r+1 : ℕ) : ℝ) = -e := by dsimp [e]; push_cast; ring
    simpa only [heq] using (h f hf A hA hh m hm z hz).2
  have hordered (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
      (hxy : delta m y ≤ delta m x) :
      ‖(derivative^[r] Q).eval (x : ℂ)-(derivative^[r] Q).eval (y : ℂ)‖ ≤
        (2*K+1)*A*|x-y|^θ := by
    by_cases hnear : |x-y| ≤ delta m x
    · have hb (z : ℝ) (hz : z ∈ Set.uIcc x y) :
          ‖(derivative^[r+1] Q).eval (z : ℂ)‖ ≤ 2*K*A*delta m x^(-e) := by
        have hzi := (Set.uIcc_subset_Icc hx hy) hz
        have hd0 : |x-z| ≤ |x-y| := by
          simpa only [abs_sub_comm] using Set.abs_sub_left_of_mem_uIcc hz
        have hd : |x-z| ≤ delta m x := hd0.trans hnear
        have hs := negative_delta_comparison hm hx hzi he he1
        have hr : |x-z|/delta m x ≤ 1 := (div_le_one (delta_pos hm x)).mpr hd
        calc
          _ ≤ K*A*delta m z^(-e) := hhigh z hzi
          _ ≤ K*A*(delta m x^(-e)*(1+|x-z|/delta m x)) := by gcongr
          _ ≤ K*A*(delta m x^(-e)*2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith :
              1+|x-z|/delta m x ≤ 2) (Real.rpow_nonneg (delta_pos hm x).le _))
              (mul_nonneg hK.le hA)
          _ = _ := by ring
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ Set.uIcc x y) => by
          simpa only [Function.iterate_succ_apply'] using
            ((derivative^[r] Q).hasDerivAt (z : ℂ)).comp_ofReal.hasDerivWithinAt)
        hb (convex_uIcc x y) Set.left_mem_uIcc Set.right_mem_uIcc
      rw [norm_sub_rev,Real.norm_eq_abs,abs_sub_comm y x] at hmvt
      have hscale : delta m x^(-e)*|x-y| ≤ |x-y|^θ := by
        by_cases hzero : |x-y|=0
        · simp [hzero,Real.zero_rpow (by dsimp [θ]; linarith : θ ≠ 0)]
        · have hd : 0 < |x-y| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
          calc
            _ ≤ |x-y|^(-e)*|x-y| := mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_nonpos hd hnear (neg_nonpos.mpr he)) (abs_nonneg _)
            _ = _ := by rw [← Real.rpow_add_one hd.ne']; congr 1; dsimp [θ,e]; ring
      calc
        _ ≤ (2*K*A*delta m x^(-e))*|x-y| := hmvt
        _ = (2*K*A)*(delta m x^(-e)*|x-y|) := by ring
        _ ≤ (2*K*A)*|x-y|^θ := mul_le_mul_of_nonneg_left hscale (by positivity)
        _ ≤ _ := by gcongr; nlinarith
    · have hdx : delta m x ≤ |x-y| := (le_of_not_ge hnear)
      have hdy := hxy.trans hdx
      have ha := (h f hf A hA hh m hm x hx).1 r le_rfl
      have hb := (h f hf A hA hh m hm y hy).1 r le_rfl
      have hc := hh x hx y hy
      have htri : ‖(derivative^[r] Q).eval (x : ℂ)-(derivative^[r] Q).eval (y : ℂ)‖ ≤
          ‖F x-(derivative^[r] Q).eval (x : ℂ)‖+‖F x-F y‖+
          ‖F y-(derivative^[r] Q).eval (y : ℂ)‖ := by
        have h1 := norm_sub_le_norm_sub_add_norm_sub (derivative^[r] Q |>.eval (x : ℂ)) (F x)
          (derivative^[r] Q |>.eval (y : ℂ))
        have h2 := norm_sub_le_norm_sub_add_norm_sub (F x) (F y) (derivative^[r] Q |>.eval (y : ℂ))
        rw [norm_sub_rev _ (F x)] at h1
        linarith
      have hpx := Real.rpow_le_rpow (delta_pos hm x).le hdx hθ
      have hpy := Real.rpow_le_rpow (delta_pos hm y).le hdy hθ
      calc
        _ ≤ K*A*delta m x^θ+A*|x-y|^θ+K*A*delta m y^θ :=
          htri.trans (add_le_add (add_le_add ha hc) hb)
        _ ≤ K*A*|x-y|^θ+A*|x-y|^θ+K*A*|x-y|^θ := by gcongr
        _ = _ := by ring
  intro x hx y hy
  rcases le_total (delta m y) (delta m x) with hxy | hyx
  · exact hordered x y hx hy hxy
  · simpa only [norm_sub_rev,abs_sub_comm] using hordered y x hy hx hyx

private lemma lorentz_two_weights (r ℓ : ℕ) (β γ : ℝ)
    (hβ : (r : ℝ) ≤ β) (hγ : (r : ℝ) ≤ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ f : ℕ → ℕ → ℂ,
      (∀ ν ≤ r, ∀ i ≤ m, ‖f ν i‖ ≤ A * |(i : ℝ)/(m : ℝ) - p| ^ (β - (ν : ℝ))+
        B * |(i : ℝ)/(m : ℝ) - p| ^ (γ - (ν : ℝ))) →
      ‖(derivative^[ℓ] (lorentzJet m r f)).eval (p : ℂ)‖ ≤
        K * (A * delta m p ^ (β - (ℓ : ℝ)) + B * delta m p ^ (γ - (ℓ : ℝ))) := by
  obtain ⟨C,hC,hc⟩ := lorentz_jet_derivative_bound r ℓ β hβ
  obtain ⟨D,hD,hd⟩ := lorentz_jet_derivative_bound r ℓ γ hγ
  refine ⟨max C D, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro m hm p hp A B hA hB f hf
  let F := fun ν i => if ν ≤ r ∧ i ≤ m then f ν i else 0
  have hsplit (ν i : ℕ) : ∃ u v : ℂ,
      ‖u‖ ≤ A*|(i : ℝ)/(m : ℝ)-p|^(β-(ν : ℝ)) ∧
      ‖v‖ ≤ B*|(i : ℝ)/(m : ℝ)-p|^(γ-(ν : ℝ)) ∧ u+v=F ν i := by
    have hb : ‖F ν i‖ ≤ A*|(i : ℝ)/(m : ℝ)-p|^(β-(ν : ℝ))+
        B*|(i : ℝ)/(m : ℝ)-p|^(γ-(ν : ℝ)) := by
      dsimp [F]
      split_ifs with h
      · exact hf ν h.1 i h.2
      · simp only [norm_zero]; positivity
    have hmem : F ν i ∈ Metric.closedBall (0+0 : ℂ)
        (A*|(i : ℝ)/(m : ℝ)-p|^(β-(ν : ℝ))+B*|(i : ℝ)/(m : ℝ)-p|^(γ-(ν : ℝ))) := by
      simpa only [Metric.mem_closedBall,zero_add,dist_zero_right] using hb
    rw [← closedBall_add_closedBall (by positivity) (by positivity)] at hmem
    obtain ⟨u,hu,v,hv,he⟩ := hmem
    exact ⟨u,v,by simpa only [Metric.mem_closedBall,dist_zero_right] using hu,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hv,he⟩
  choose U V hU hV hUV using hsplit
  have hQ : lorentzJet m r f = lorentzJet m r U+lorentzJet m r V := by
    unfold lorentzJet
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro ν hν
    rw [← mul_add,← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [← add_mul,← map_add,hUV]
    have hlegal : ν ≤ r ∧ i ≤ m :=
      ⟨Nat.le_of_lt_succ (mem_range.mp hν), Nat.le_of_lt_succ (mem_range.mp hi)⟩
    simp only [F,if_pos hlegal]
  calc
    _ = ‖(derivative^[ℓ] (lorentzJet m r U)).eval (p : ℂ)+
        (derivative^[ℓ] (lorentzJet m r V)).eval (p : ℂ)‖ := by
      rw [hQ]
      simp only [← Module.End.pow_apply,map_add,eval_add]
    _ ≤ ‖(derivative^[ℓ] (lorentzJet m r U)).eval (p : ℂ)‖+
        ‖(derivative^[ℓ] (lorentzJet m r V)).eval (p : ℂ)‖ := norm_add_le _ _
    _ ≤ C*A*delta m p^(β-(ℓ : ℝ))+D*B*delta m p^(γ-(ℓ : ℝ)) :=
      add_le_add (hc m hm p hp A hA U (fun ν _ i _ => hU ν i))
        (hd m hm p hp B hB V (fun ν _ i _ => hV ν i))
    _ ≤ _ := by
      rw [mul_add]
      apply add_le_add <;> simp only [← mul_assoc]
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C D) hA)
          (Real.rpow_nonneg (delta_pos hm p).le _)
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C D) hB)
          (Real.rpow_nonneg (delta_pos hm p).le _)

/-- Stability of the actual Lorentz operator for a derivative bounded by a
negative endpoint-scale power. The constant is uniform in the grid and polynomial. -/
theorem weighted_lorentz_stability (r : ℕ) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ A : ℝ, 0 ≤ A → ∀ V : ℂ[X],
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖(derivative^[r + 1] V).eval (x : ℂ)‖ ≤ A * delta m x ^ (-e)) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        ‖(derivative^[r + 1] (lorentzOperator m r V)).eval (p : ℂ)‖ ≤ K * A * delta m p ^ (-e) := by
  obtain ⟨K,hK,hbound⟩ := lorentz_two_weights r (r+1) ((r : ℝ)+1) ((r : ℝ)+2)
    (by linarith) (by linarith)
  refine ⟨2*K,by positivity,?_⟩
  intro m hm A hA V hV p hp
  have hR := delta_pos hm p
  obtain ⟨P,hdeg,hP⟩ := exists_taylor_jet r (p : ℂ)
    (fun j => (derivative^[j] V).eval (p : ℂ))
  let g := fun j (x : ℝ) => (derivative^[j] (V-P)).eval (x : ℂ)
  have htop (x : ℝ) : g (r+1) x = (derivative^[r+1] V).eval (x : ℂ) := by
    simp only [g,iterate_derivative_sub,
      iterate_derivative_eq_zero (by omega : P.natDegree < r+1),sub_zero]
  have hgrid (ν : ℕ) (hν : ν ≤ r) (i : ℕ) (hi : i ≤ m) :
      ‖g ν ((i : ℝ)/(m : ℝ))‖ ≤
        (A*delta m p^(-e))*|(i : ℝ)/(m : ℝ)-p|^((r : ℝ)+1-(ν : ℝ))+
        (A*delta m p^(-e)/delta m p)*|(i : ℝ)/(m : ℝ)-p|^((r : ℝ)+2-(ν : ℝ)) := by
    let x := (i : ℝ)/(m : ℝ)
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [x]; positivity
      · exact (div_le_one (by exact_mod_cast hm : (0 : ℝ)<m)).mpr (by exact_mod_cast hi)
    let B := A*delta m p^(-e)*(1+|x-p|/delta m p)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hd (j : ℕ) (_ : j < r+1) (y : ℝ) (_ : y ∈ Set.uIcc p x) :
        HasDerivWithinAt (g j) (g (j+1) y) (Set.uIcc p x) y := by
      simpa only [g,Function.iterate_succ_apply'] using
        ((derivative^[j] (V-P)).hasDerivAt (y : ℂ)).comp_ofReal.hasDerivWithinAt
    have hz (j : ℕ) (hj : j < r+1) : g j p = 0 := by
      simp only [g,iterate_derivative_sub,eval_sub,hP j (by omega),sub_self]
    have ht (y : ℝ) (hy : y ∈ Set.uIcc p x) :
        ‖g (r+1) y‖ ≤ B*|y-p|^(((r+1 : ℕ) : ℝ)-((r+1 : ℕ) : ℝ)) := by
      have hyI := Set.uIcc_subset_Icc hp hx hy
      have hdist : |p-y| ≤ |x-p| := by
        simpa only [abs_sub_comm] using Set.abs_sub_left_of_mem_uIcc hy
      rw [htop,sub_self,Real.rpow_zero,mul_one]
      calc
        _ ≤ A*delta m y^(-e) := hV y hyI
        _ ≤ A*(delta m p^(-e)*(1+|p-y|/delta m p)) :=
          mul_le_mul_of_nonneg_left (negative_delta_comparison hm hp hyI he he1) hA
        _ ≤ B := by dsimp [B]; rw [mul_assoc]; gcongr
    have hb := vanishing_jet_bound (convex_uIcc p x) (le_refl ((r+1 : ℕ) : ℝ))
      hB Set.left_mem_uIcc g hd hz ht ν (by omega) x Set.right_mem_uIcc
    have hpow : |x-p|^((r : ℝ)+2-(ν : ℝ)) = |x-p|^((r : ℝ)+1-(ν : ℝ))*|x-p| := by
      have hexp : 0 ≤ (r : ℝ)+1-(ν : ℝ) := by
        have : (ν : ℝ) ≤ r := by exact_mod_cast hν
        linarith
      rw [show (r : ℝ)+2-(ν : ℝ)=((r : ℝ)+1-(ν : ℝ))+1 by ring,
        Real.rpow_add_of_nonneg (abs_nonneg _) hexp (by norm_num),Real.rpow_one]
    calc
      _ ≤ B*|x-p|^(((r+1 : ℕ) : ℝ)-(ν : ℝ)) := hb
      _ = _ := by change _ = _ + (A*delta m p^(-e)/delta m p)*|x-p|^_
                  rw [hpow]; dsimp [B]; push_cast; ring
  have hb := hbound m hm p hp (A*delta m p^(-e)) (A*delta m p^(-e)/delta m p)
    (by positivity) (by positivity) (fun ν i => g ν ((i : ℝ)/(m : ℝ))) hgrid
  have hQ : lorentzJet m r (fun ν i => g ν ((i : ℝ)/(m : ℝ))) = lorentzOperator m r V-P := by
    convert lorentz_jet_sub_polynomial hm
      (fun j x => (derivative^[j] V).eval (x : ℂ)) P hdeg using 1 <;>
      simp only [g,lorentzOperator,iterate_derivative_sub,eval_sub,
        Complex.ofReal_div,Complex.ofReal_natCast]
  rw [hQ,iterate_derivative_sub,
    iterate_derivative_eq_zero (by omega : P.natDegree < r+1),sub_zero] at hb
  have h1 : (r : ℝ)+1-((r+1 : ℕ) : ℝ)=0 := by push_cast; ring
  have h2 : (r : ℝ)+2-((r+1 : ℕ) : ℝ)=1 := by push_cast; ring
  rw [h1,h2,Real.rpow_zero,Real.rpow_one,mul_one] at hb
  calc
    _ ≤ K*(A*delta m p^(-e)+(A*delta m p^(-e)/delta m p)*delta m p) := hb
    _ = _ := by rw [div_mul_cancel₀ _ hR.ne']; ring

end D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
