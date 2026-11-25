/- GID: D5/S3/Analytic/Laplace/SignedMoments
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/SignedMoments
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [mathlib/module/Mathlib.Probability.Moments.ComplexMGF]
   utility: none
   digest: Signed Laplace derivatives and their one-sided positive moment bound. -/

import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.Continuation
import Mathlib.Probability.Moments.ComplexMGF

/-! # Signed Laplace moments

Absolute convergence throughout a real half-line controls every polynomial
moment locally. The signed transform can therefore be differentiated without
any positivity assumption on its density. Its complex moment and real signed
moment together are bounded by twice the positive-part moment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open D5.S3.Analytic.Laplace.PairedPoleRegularity (laplace)
open D5.S3.Analytic.Laplace.QuantitativeFejerBoundary

namespace D5.S3.Analytic.Laplace.SignedMoments

/-- An unnormalized complex moment of the actual signed Laplace integral. -/
def moment (h : ℝ → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ u in Ici (0 : ℝ), (u : ℂ) ^ k * (h u : ℂ) * Complex.exp (-z * u)

private theorem abs_convergence {h : ℝ → ℝ} {σ : ℝ}
    (hi : IntegrableOn (fun u => h u * Real.exp (-σ * u)) (Ici 0)) :
    IntegrableOn (fun u => |h u| * Real.exp (-σ * u)) (Ici 0) := by
  simpa [IntegrableOn, Real.norm_eq_abs] using hi.norm

/-- Absolute exponential convergence also gives every absolute polynomial moment. -/
theorem absolute_moment_integrable {h : ℝ → ℝ} {a σ : ℝ}
    (hm : Measurable h)
    (hc : ∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0))
    (hσ : a < σ) (k : ℕ) :
    IntegrableOn (fun u => u ^ k * |h u| * Real.exp (-σ * u)) (Ici 0) := by
  let μ := rayMeasure (fun u => |h u|)
  have hmabs : Measurable (fun u => |h u|) := by fun_prop
  have hmem : -σ ∈ interior (integrableExpSet id μ) := by
    apply mem_interior.mpr
    refine ⟨Iio (-a), ?_, isOpen_Iio, by simp only [mem_Iio]; linarith⟩
    intro t ht
    apply (ray_integrable_iff hmabs (fun _ _ => abs_nonneg _) t).mpr
    simpa only [neg_neg] using abs_convergence (hc (-t) (by
      change t < -a at ht
      linarith))
  have hi := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem k
  change Integrable _ (rayMeasure (fun u => |h u|)) at hi
  rw [rayMeasure, integrable_withDensity_iff_integrable_smul'
    hmabs.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hi
  apply hi.congr
  filter_upwards [] with u
  simp only [id_eq, ENNReal.toReal_ofReal (abs_nonneg (h u)), smul_eq_mul]
  ring

private theorem integrand_norm (h : ℝ → ℝ) (k : ℕ) (z : ℂ)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖(u : ℂ) ^ k * (h u : ℂ) * Complex.exp (-z * u)‖ =
      u ^ k * |h u| * Real.exp (-z.re * u) := by
  simp [norm_pow, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hu]

/-- Complex moments converge wherever the real exponential integral does locally. -/
theorem moment_integrable {h : ℝ → ℝ} {a : ℝ} {z : ℂ}
    (hm : Measurable h)
    (hc : ∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0))
    (hz : a < z.re) (k : ℕ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ k * (h u : ℂ) *
      Complex.exp (-z * u)) (Ici 0) := by
  apply (absolute_moment_integrable hm hc hz k).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact (integrand_norm h k z hu).le

/-- Dominated differentiation increases the moment order and introduces a minus sign. -/
theorem moment_hasDerivAt {h : ℝ → ℝ} {a : ℝ} {z : ℂ}
    (hm : Measurable h)
    (hc : ∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0))
    (hz : a < z.re) (k : ℕ) :
    HasDerivAt (moment h k) (-moment h (k + 1) z) z := by
  let b := (a + z.re) / 2
  have hb : a < b := by dsimp [b]; linarith
  have hbz : b < z.re := by dsimp [b]; linarith
  let V : Set ℂ := {w | b < w.re}
  have hV : V ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hbz
  let F : ℂ → ℝ → ℂ := fun w u =>
    (u : ℂ) ^ k * (h u : ℂ) * Complex.exp (-w * u)
  let F' : ℂ → ℝ → ℂ := fun w u =>
    -((u : ℂ) ^ (k + 1) * (h u : ℂ) * Complex.exp (-w * u))
  have hd : HasDerivAt (fun w => ∫ u in Ici (0 : ℝ), F w u)
      (∫ u in Ici (0 : ℝ), F' z u) z := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') hV
      (Eventually.of_forall fun w => by dsimp [F]; fun_prop)
      (moment_integrable hm hc hz k)
      (by dsimp [F']; fun_prop)
      (bound := fun u => u ^ (k + 1) * |h u| * Real.exp (-b * u)) ?_
      (absolute_moment_integrable hm hc hb (k + 1)) ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      intro w hw
      have hu0 : 0 ≤ u := hu
      change b < w.re at hw
      dsimp [F']
      rw [norm_neg, integrand_norm h (k + 1) w hu0]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (neg_le_neg hw.le) hu0)
    · filter_upwards [] with u
      intro w _
      have he := (((hasDerivAt_id w).neg.mul_const (u : ℂ)).cexp).const_mul
        ((u : ℂ) ^ k * (h u : ℂ))
      convert he using 1 <;> dsimp [F, F']
      simp only [pow_succ]
      ring
  simp only [F, F', integral_neg] at hd
  exact hd

/-- Every derivative is the corresponding actual signed moment. -/
theorem iteratedDeriv_laplace {h : ℝ → ℝ} {a : ℝ} {z : ℂ}
    (hm : Measurable h)
    (hc : ∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0))
    (hz : a < z.re) (k : ℕ) :
    iteratedDeriv k (laplace h) z = (-1 : ℂ) ^ k * moment h k z := by
  induction k generalizing z with
  | zero => simp [laplace, moment]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (laplace h) =ᶠ[𝓝 z]
        fun w => (-1 : ℂ) ^ k * moment h k w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw using ih hw
    rw [he.deriv_eq, ((moment_hasDerivAt hm hc hz k).const_mul ((-1 : ℂ) ^ k)).deriv]
    simp only [pow_succ]
    ring

/-- At a real center the alternating derivative is the actual real signed moment. -/
theorem alternating_derivative_real {h : ℝ → ℝ} {a σ : ℝ}
    (hm : Measurable h)
    (hc : ∀ t : ℝ, a < t →
      IntegrableOn (fun u => h u * Real.exp (-t * u)) (Ici 0))
    (hσ : a < σ) (k : ℕ) :
    (((-1 : ℂ) ^ k * iteratedDeriv k (laplace h) (σ : ℂ)) /
        (k.factorial : ℂ)).re =
      (∫ u in Ici (0 : ℝ), u ^ k * h u * Real.exp (-σ * u)) / k.factorial := by
  rw [iteratedDeriv_laplace hm hc (by simpa using hσ) k]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsign, one_mul]
  have he : moment h k (σ : ℂ) =
      ((∫ u in Ici (0 : ℝ), u ^ k * h u * Real.exp (-σ * u)) : ℝ) := by
    calc
      _ = ∫ u in Ici (0 : ℝ),
          ((u ^ k * h u * Real.exp (-σ * u) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [show -(σ : ℂ) * (u : ℂ) = ((-σ * u : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp]
        push_cast
        rfl
      _ = _ := integral_ofReal
  rw [he]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]

/-- The complex moment plus the real signed moment is controlled by its positive part.
For a nonintegrable signed moment both signed integrals use the total value zero. -/
theorem moment_norm_add_real_le {h : ℝ → ℝ} {z : ℂ} (k : ℕ) :
    ‖moment h k z‖ +
        (∫ u in Ici (0 : ℝ), u ^ k * h u * Real.exp (-z.re * u)) ≤
      2 * ∫ u in Ici (0 : ℝ), u ^ k * max (h u) 0 * Real.exp (-z.re * u) := by
  by_cases hsigned : IntegrableOn
      (fun u => u ^ k * h u * Real.exp (-z.re * u)) (Ici 0)
  ·
    have habs : IntegrableOn
        (fun u => u ^ k * |h u| * Real.exp (-z.re * u)) (Ici 0) := by
      apply hsigned.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      have hu0 : 0 ≤ u := hu
      simp [Real.norm_eq_abs, abs_of_nonneg hu0]
    have hnorm : ‖moment h k z‖ ≤
        ∫ u in Ici (0 : ℝ), u ^ k * |h u| * Real.exp (-z.re * u) := by
      apply (norm_integral_le_integral_norm _).trans_eq
      apply setIntegral_congr_fun measurableSet_Ici
      intro u hu
      exact integrand_norm h k z hu
    calc
      _ ≤ (∫ u in Ici (0 : ℝ), u ^ k * |h u| * Real.exp (-z.re * u)) +
          ∫ u in Ici (0 : ℝ), u ^ k * h u * Real.exp (-z.re * u) :=
        by linarith
      _ = ∫ u in Ici (0 : ℝ), 2 * (u ^ k * max (h u) 0 *
          Real.exp (-z.re * u)) := by
        rw [← integral_add habs hsigned]
        apply integral_congr_ae
        filter_upwards [] with u
        have he : |h u| + h u = 2 * max (h u) 0 := by
          rcases le_total 0 (h u) with hp | hn
          · rw [abs_of_nonneg hp, max_eq_left hp]; ring
          · rw [abs_of_nonpos hn, max_eq_right hn]; ring
        calc
          _ = u ^ k * (|h u| + h u) * Real.exp (-z.re * u) := by ring
          _ = _ := by rw [he]; ring
      _ = _ := integral_const_mul 2 _
  · have hcomplex : ¬ IntegrableOn
        (fun u : ℝ => (u : ℂ) ^ k * (h u : ℂ) * Complex.exp (-z * u)) (Ici 0) := by
      intro hi
      let phase : ℝ → ℂ := fun u => Complex.exp ((z - (z.re : ℂ)) * u)
      have hp : Continuous phase := by dsimp [phase]; fun_prop
      have hn (u : ℝ) : ‖phase u‖ ≤ 1 := by
        simp [phase, Complex.norm_exp, Complex.mul_re]
      have hj := (hi.mul_bdd hp.aestronglyMeasurable (ae_of_all _ hn)).re
      apply hsigned
      apply hj.congr
      filter_upwards [] with u
      symm
      dsimp [phase]
      simp only [mul_assoc]
      rw [← Complex.exp_add]
      rw [show -z * (u : ℂ) + (z - (z.re : ℂ)) * u =
        ((-z.re * u : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp]
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_assoc]
    rw [moment, integral_undef hcomplex, integral_undef hsigned, norm_zero, zero_add]
    apply mul_nonneg (by norm_num)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact mul_nonneg (mul_nonneg (pow_nonneg hu k) (le_max_right _ _)) (Real.exp_pos _).le

end D5.S3.Analytic.Laplace.SignedMoments
