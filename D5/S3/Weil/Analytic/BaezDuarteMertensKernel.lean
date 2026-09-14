/- GID: D5/S3/Weil/Analytic/BaezDuarteMertensKernel
   generality: G
   mirror-B: D5/B/S3/Weil/Analytic/BaezDuarteMertensKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The inverse-square coefficient kernel has a beta integral and uniform power bound. -/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.LiminfLimsup

/-! Coefficient-specific kernels for the signed Abel transfer. The beta bound
uses the public Euler sequence, without a new Gamma asymptotic. The inverse-square
substitution retains its factor one half. Utility none: general analytic estimates. -/

open scoped Topology Real
open Filter MeasureTheory Set

namespace D5.S3.Weil.Analytic.BaezDuarteMertensKernel

/-- A single constant bounds the entire positive-index beta sequence. -/
theorem baez_duarte_beta_bound (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖Complex.betaIntegral (b : ℂ) ((k : ℂ)+1)‖ ≤ C * Real.rpow (k : ℝ) (-b) := by
  obtain ⟨C, hC⟩ := (Complex.GammaSeq_tendsto_Gamma (b : ℂ)).norm.bddAbove_range
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun k hk => ?_⟩
  have hbound := hC (Set.mem_range_self k)
  rw [Complex.GammaSeq_eq_betaIntegral_of_re_pos (by simpa using hb), norm_mul,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast hk), Complex.ofReal_re] at hbound
  simp only [Complex.ofReal_natCast] at hbound
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hp := Real.rpow_pos_of_pos hkpos b
  calc
    _ ≤ C / Real.rpow (k : ℝ) b := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hbound)
    _ ≤ max C 1 / Real.rpow (k : ℝ) b := div_le_div_of_nonneg_right (le_max_left _ _) hp.le
    _ = max C 1 * Real.rpow (k : ℝ) (-b) := by simp only [Real.rpow_eq_pow, Real.rpow_neg hkpos.le, div_eq_mul_inv]

/-- The derivative has the negative first term and the original index. -/
theorem baez_duarte_kernel_hasDerivAt (k : ℕ) (_hk : 1 ≤ k) (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt (fun x : ℝ => x⁻¹^2*(1-x⁻¹^2)^k)
      (-2*x⁻¹^3*(1-x⁻¹^2)^k + 2*(k : ℝ)*x⁻¹^5*(1-x⁻¹^2)^(k-1)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hi := (hasDerivAt_id x).inv hx0
  have hsq := hi.pow 2
  convert hsq.mul ((hsq.const_sub 1).pow k) using 1 <;> try rfl
  simp only [Pi.pow_apply, Pi.inv_apply, id_eq, Nat.cast_ofNat, pow_one, Nat.reduceSub]
  rw [div_eq_mul_inv, inv_pow]
  ring
private theorem beta_integrand_real (b x : ℝ) (k : ℕ) (hx : 0 ≤ x) :
    (x : ℂ)^((b : ℂ)-1) * (1-(x : ℂ))^(((k : ℂ)+1)-1) =
      ((Real.rpow x (b-1) * (1-x)^k : ℝ) : ℂ) := by
  rw [add_sub_cancel_right, Complex.cpow_natCast]
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  congr 1
  simpa only [Real.rpow_eq_pow, Complex.ofReal_sub, Complex.ofReal_one] using (Complex.ofReal_cpow hx (b-1)).symm

private theorem beta_integrable (b : ℝ) (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun x : ℝ => Real.rpow x (b-1)*(1-x)^k) (Ioo 0 1) := by
  have h := Complex.betaIntegral_convergent (u := (b : ℂ)) (v := (k : ℂ)+1)
    (by simpa using hb) (by simp; positivity)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integrableOn_Ioc_iff_integrableOn_Ioo] at h
  have hreal : IntegrableOn (fun x : ℝ =>
      ( (x : ℂ)^((b : ℂ)-1) * (1-(x : ℂ))^(((k : ℂ)+1)-1)).re) (Ioo 0 1) := h.re
  exact hreal.congr_fun (fun x hx => by dsimp only; rw [beta_integrand_real b x k hx.1.le, Complex.ofReal_re])
    measurableSet_Ioo

private theorem beta_integral_real (b : ℝ) (k : ℕ) :
    (∫ x : ℝ in Ioo 0 1, Real.rpow x (b-1)*(1-x)^k) =
      (Complex.betaIntegral (b : ℂ) ((k : ℂ)+1)).re := by
  have he : Complex.betaIntegral (b : ℂ) ((k : ℂ)+1) =
      ((∫ x : ℝ in Ioo 0 1, Real.rpow x (b-1)*(1-x)^k) : ℝ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo]
    calc
      _ = ∫ x : ℝ in Ioo 0 1, ((Real.rpow x (b-1)*(1-x)^k : ℝ) : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioo fun x hx => beta_integrand_real b x k hx.1.le
      _ = _ := integral_complex_ofReal
  rw [he, Complex.ofReal_re]

private theorem inverse_square_image :
    (fun x : ℝ => x ^ (-2 : ℝ)) '' Ioi 1 = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Real.rpow_pos_of_pos (by linarith [show 1 < x from hx]) _,
      Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)⟩
  · intro hy
    refine ⟨y ^ (-(1 : ℝ)/2),
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg hy.1 hy.2 (by norm_num), ?_⟩
    dsimp only
    rw [← Real.rpow_mul hy.1.le]
    norm_num

private theorem inverse_square_jacobian (b x : ℝ) (k : ℕ) (hx : 1 < x) :
    |(-2 : ℝ) * x ^ ((-2 : ℝ)-1)| *
      (Real.rpow (x ^ (-2 : ℝ)) (b-1)*(1-x ^ (-2 : ℝ))^k) =
      2 * (Real.rpow x (-2*b-1)*(1-x⁻¹^2)^k) := by
  have hx0 : 0 < x := by linarith
  have hinv : x ^ (-2 : ℝ) = x⁻¹^2 := by
    rw [Real.rpow_neg hx0.le, Real.rpow_two, inv_pow]
  simp only [Real.rpow_eq_pow]
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_mul hx0.le]
  rw [hinv]
  calc
    _ = 2 * (x ^ (-3 : ℝ) * x ^ (-2*(b-1))) * (1-x⁻¹^2)^k := by ring
    _ = _ := by
      rw [← Real.rpow_add hx0, show (-3 : ℝ) + -2*(b-1) = -2*b-1 by ring, mul_assoc]

/-- Integrability is transported by the inverse-square Jacobian, not inferred
from a totalized integral notation. -/
theorem baez_duarte_kernel_integrable (b : ℝ) (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun x : ℝ => Real.rpow x (-2*b-1)*(1-x⁻¹^2)^k) (Ioi 1) := by
  have hd : ∀ x ∈ Ioi (1 : ℝ), HasDerivWithinAt
      (fun x : ℝ => x ^ (-2 : ℝ)) (-2*x ^ ((-2 : ℝ)-1)) (Ioi 1) x :=
    fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (by linarith [show 1 < x from hx] : x ≠ 0))).hasDerivWithinAt
  have hi : InjOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
    (Real.rpow_left_injOn (by norm_num : (-2 : ℝ) ≠ 0)).mono (by intro x hx; change 0 ≤ x; linarith [show 1 < x from hx])
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hi
    (fun x : ℝ => Real.rpow x (b-1)*(1-x)^k)).mp
      (inverse_square_image.symm ▸ beta_integrable b hb k)
  have h' : IntegrableOn (fun x : ℝ =>
      2 * (Real.rpow x (-2*b-1)*(1-x⁻¹^2)^k)) (Ioi 1) :=
    h.congr_fun (fun x hx => by simpa only [smul_eq_mul] using inverse_square_jacobian b x k hx)
      measurableSet_Ioi
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0)) _).mp h'

/-- The beta substitution has exactly the factor one half. -/
theorem baez_duarte_kernel_integral (b : ℝ) (_hb : 0 < b) (k : ℕ) :
    (∫ x : ℝ in Ioi 1, Real.rpow x (-2*b-1)*(1-x⁻¹^2)^k) =
      (Complex.betaIntegral (b : ℂ) ((k : ℂ)+1)).re / 2 := by
  have hd : ∀ x ∈ Ioi (1 : ℝ), HasDerivWithinAt
      (fun x : ℝ => x ^ (-2 : ℝ)) (-2*x ^ ((-2 : ℝ)-1)) (Ioi 1) x :=
    fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (by linarith [show 1 < x from hx] : x ≠ 0))).hasDerivWithinAt
  have hi : InjOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
    (Real.rpow_left_injOn (by norm_num : (-2 : ℝ) ≠ 0)).mono (by intro x hx; change 0 ≤ x; linarith [show 1 < x from hx])
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hi
    (fun x : ℝ => Real.rpow x (b-1)*(1-x)^k)
  rw [inverse_square_image, beta_integral_real] at h
  have hj : (∫ x : ℝ in Ioi 1, |(-2 : ℝ)*x^((-2 : ℝ)-1)| •
      (Real.rpow (x^(-2 : ℝ)) (b-1)*(1-x^(-2 : ℝ))^k)) =
      2 * (∫ x : ℝ in Ioi 1, Real.rpow x (-2*b-1)*(1-x⁻¹^2)^k) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      inverse_square_jacobian b x k hx
  rw [hj] at h
  linarith


/-- The two derivative terms have one index-independent power bound. -/
theorem baez_duarte_beta_combined_bound (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      (Complex.betaIntegral (b : ℂ) ((k : ℂ)+1)).re +
        (k : ℝ)*(Complex.betaIntegral ((b : ℂ)+1) (k : ℂ)).re ≤
          C * Real.rpow (k : ℝ) (-b) := by
  obtain ⟨C, hC, hbound⟩ := baez_duarte_beta_bound b hb
  refine ⟨(1+b)*C, mul_pos (by linarith) hC, fun k hk => ?_⟩
  have he := congrArg Complex.re (Complex.betaIntegral_recurrence
    (u := (b : ℂ)) (v := (k : ℂ)) (by simpa using hb)
    (by simpa using (show (0 : ℝ) < k by exact_mod_cast hk)))
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at he
  have hr : (Complex.betaIntegral (b : ℂ) ((k : ℂ)+1)).re ≤
      C * Real.rpow (k : ℝ) (-b) :=
    (Complex.re_le_norm _).trans (hbound k hk)
  have hnon : 0 ≤ 1+b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hr hnon]

end D5.S3.Weil.Analytic.BaezDuarteMertensKernel
