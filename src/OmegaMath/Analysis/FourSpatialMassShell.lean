import OmegaBuild.Commands
import OmegaMath.Analysis.HalfIntegerSchwingerIntegral
import OmegaMath.Analysis.GaussianSubordination
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
Omega original.

The regulated momentum integral on four-dimensional Euclidean space and its
continuation from positive Euclidean time.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped InnerProductSpace Topology

namespace Omega

namespace FourSpatialMassShell

abbrev E := EuclideanSpace ℝ (Fin 4)

def energy (M : ℝ) (k : E) : ℝ := Real.sqrt (‖k‖ ^ 2 + M ^ 2)

/-- The invariant shell density, with value zero at the massless zero momentum. -/
def shellWeight (M : ℝ) (k : E) : ℝ := 1 / (2 * (2 * Real.pi) ^ 4 * energy M k)

def bulkU5D (M : ℝ) (τ : ℂ) (r : E) : ℂ :=
  ∫ k : E, (shellWeight M k : ℂ) *
    Complex.exp (-τ * (energy M k : ℂ) + I * (⟪k, r⟫_ℝ : ℂ))

private abbrev shellIntegrand (M : ℝ) (τ : ℂ) (r k : E) : ℂ :=
  (shellWeight M k : ℂ) * Complex.exp (-τ * (energy M k : ℂ) + I * (⟪k, r⟫_ℝ : ℂ))

private theorem norm_le_energy (M : ℝ) (k : E) : ‖k‖ ≤ energy M k := by
  calc
    ‖k‖ = Real.sqrt (‖k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg k)).symm
    _ ≤ energy M k := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg M))

private theorem energy_nonneg (M : ℝ) (k : E) : 0 ≤ energy M k :=
  (norm_nonneg k).trans (norm_le_energy M k)

private theorem energy_pos (M : ℝ) {k : E} (hk : k ≠ 0) : 0 < energy M k :=
  (norm_pos_iff.mpr hk).trans_le (norm_le_energy M k)

private theorem shellWeight_nonneg (M : ℝ) (k : E) : 0 ≤ shellWeight M k :=
  div_nonneg zero_le_one (mul_nonneg (by positivity) (energy_nonneg M k))

private theorem shellIntegrand_measurable (M : ℝ) (τ : ℂ) (r : E) :
    Measurable (shellIntegrand M τ r) := by
  unfold shellIntegrand shellWeight energy
  fun_prop

private theorem norm_shellIntegrand (M : ℝ) (τ : ℂ) (r k : E) :
    ‖shellIntegrand M τ r k‖ = shellWeight M k * Real.exp (-τ.re * energy M k) := by
  rw [shellIntegrand, norm_mul, Complex.norm_real, Real.norm_of_nonneg (shellWeight_nonneg M k),
    Complex.norm_exp]
  congr 2
  simp [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private theorem radial_exp_integrable {d : ℝ} (hd : 0 < d) :
    Integrable (fun k : E => Real.exp (-d * ‖k‖)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure E)
    (f := fun x => Real.exp (-d * x))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 3)
    (by norm_num) (by norm_num) hd
  simpa [E, finrank_euclideanSpace, Real.rpow_natCast, Real.rpow_one, smul_eq_mul, neg_mul] using h

private theorem radial_inv_exp_integrable {d : ℝ} (hd : 0 < d) :
    Integrable (fun k : E => ‖k‖⁻¹ * Real.exp (-d * ‖k‖)) := by
  -- The four-dimensional radial Jacobian cancels the inverse radius at the origin.
  apply (integrable_fun_norm_addHaar (volume : Measure E)
    (f := fun x => x⁻¹ * Real.exp (-d * x))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2)
    (by norm_num) (by norm_num) hd
  refine (h.congr_fun ?_ measurableSet_Ioi)
  intro x hx
  simp only [Real.rpow_one, Real.rpow_two, E, finrank_euclideanSpace, Fintype.card_fin,
    Nat.reduceSub, smul_eq_mul]
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp
  <;> ring

private theorem shell_ae_ne_zero : ∀ᵐ k : E, k ≠ 0 := by
  rw [ae_iff]
  simp

theorem bulkU5D_integrable (M : ℝ) {τ : ℂ} (hτ : 0 < τ.re) (r : E) :
    Integrable (fun k : E => (shellWeight M k : ℂ) *
      Complex.exp (-τ * (energy M k : ℂ) + I * (⟪k, r⟫_ℝ : ℂ))) := by
  let c : ℝ := (2 * (2 * Real.pi)^4)⁻¹
  change Integrable (shellIntegrand M τ r)
  refine ((radial_inv_exp_integrable hτ).const_mul c).mono'
    (shellIntegrand_measurable M τ r).aestronglyMeasurable ?_
  filter_upwards [shell_ae_ne_zero] with k hk
  rw [norm_shellIntegrand]
  calc
    shellWeight M k * Real.exp (-τ.re * energy M k)
        ≤ (c * ‖k‖⁻¹) * Real.exp (-τ.re * ‖k‖) := by
      refine mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by dsimp [c]; positivity)
      · unfold shellWeight
        simp only [one_div, mul_inv_rev]
        rw [mul_comm (energy M k)⁻¹]
        have hc : ((2 * Real.pi)^4)⁻¹ * (2 : ℝ)⁻¹ = c := by simp only [c, mul_inv_rev]
        rw [hc]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ (energy_pos M hk) (norm_pos_iff.mpr hk)).2 (norm_le_energy M k))
          (show 0 ≤ c by positivity)
      · exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left (norm_le_energy M k) (by linarith))
    _ = _ := mul_assoc _ _ _

private theorem shellWeight_energy_le (M : ℝ) (k : E) :
    shellWeight M k * energy M k ≤ (2 * (2 * Real.pi)^4)⁻¹ := by
  rcases eq_or_ne (energy M k) 0 with h | h
  · simpa only [h, mul_zero] using (by positivity : 0 ≤ (2 * (2 * Real.pi)^4)⁻¹)
  · simp only [shellWeight, one_div, mul_inv_rev]
    rw [mul_comm (energy M k)⁻¹, mul_assoc, inv_mul_cancel₀ h, mul_one]

theorem bulkU5D_differentiableOn (M : ℝ) (r : E) :
    DifferentiableOn ℂ (fun τ => bulkU5D M τ r) {τ : ℂ | 0 < τ.re} := by
  intro τ hτ
  change 0 < τ.re at hτ
  let c : ℝ := (2 * (2 * Real.pi)^4)⁻¹
  let d : ℝ := τ.re / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let s : Set ℂ := {z | d < z.re}
  have hs : s ∈ 𝓝 τ := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show d < τ.re by dsimp [d]; linarith)
  let F (z : ℂ) (k : E) := shellIntegrand M z r k
  -- Differentiation supplies the factor of energy needed to cancel the shell denominator.
  let F' (z : ℂ) (k : E) := -(energy M k : ℂ) * F z k
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) :=
    (shellIntegrand_measurable M z r).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' τ) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ (shellIntegrand_measurable M τ r)
    unfold energy
    fun_prop
  have hbound : ∀ᵐ k : E, ∀ z ∈ s, ‖F' z k‖ ≤ c * Real.exp (-d * ‖k‖) :=
    .of_forall fun k z hz => by
      change d < z.re at hz
      change ‖-(energy M k : ℂ) * shellIntegrand M z r k‖ ≤ _
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (energy_nonneg M k),
        norm_shellIntegrand]
      rw [← mul_assoc, mul_comm (energy M k)]
      refine mul_le_mul (shellWeight_energy_le M k) (Real.exp_le_exp.mpr ?_)
        (Real.exp_nonneg _) (by positivity)
      simp only [neg_mul, neg_le_neg_iff]
      exact (mul_le_mul_of_nonneg_right hz.le (norm_nonneg k)).trans
        (mul_le_mul_of_nonneg_left (norm_le_energy M k) (hd.le.trans hz.le))
  have hdiff : ∀ᵐ k : E, ∀ z ∈ s, HasDerivAt (F · k) (F' z k) z :=
    .of_forall fun k z _ => by
      have h := (((hasDerivAt_id z).neg.mul_const (energy M k : ℂ)).add_const
        (I * (⟪k, r⟫_ℝ : ℂ))).cexp.const_mul (shellWeight M k : ℂ)
      have he : (fun x => (shellWeight M k : ℂ) *
          Complex.exp ((-id) x * (energy M k : ℂ) + I * (⟪k, r⟫_ℝ : ℂ))) = (F · k) := rfl
      rw [he] at h
      convert h using 1
      change -↑(energy M k) * shellIntegrand M z r k = _
      simp only [Pi.neg_apply, id_eq, neg_one_mul, shellIntegrand]
      ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs (.of_forall hmeas)
    (bulkU5D_integrable M hτ r) hmeas' hbound ((radial_exp_integrable hd).const_mul c)
    hdiff).2.differentiableAt.differentiableWithinAt

private theorem energy_inv_smul (m L : ℝ) (hL : 0 < L) (k : E) :
    energy m (L⁻¹ • k) = L⁻¹ * energy (m * L) k := by
  simp only [energy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
  have he : (L⁻¹ * ‖k‖)^2 + m^2 = L⁻¹ ^ 2 * (‖k‖ ^ 2 + (m * L)^2) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg (L⁻¹)), Real.sqrt_sq (inv_nonneg.mpr hL.le)]

/-- The regulator and spatial separation scale together with inverse momentum. -/
theorem bulkU5D_scale (m L : ℝ) (hL : 0 < L)
    (τ : ℂ) (r : E) :
    bulkU5D m ((L : ℂ) * τ) (L • r) = ((L : ℂ)^3)⁻¹ * bulkU5D (m * L) τ r := by
  let f := shellIntegrand m ((L : ℂ) * τ) (L • r)
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hdim : Module.finrank ℝ E = 4 := by simp [E]
  have hJ := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E) f hL.le
  rw [hdim] at hJ
  have hf (k : E) : f (L⁻¹ • k) = (L : ℂ) * shellIntegrand (m * L) τ r k := by
    have hw : shellWeight m (L⁻¹ • k) = L * shellWeight (m * L) k := by
      simp only [shellWeight, energy_inv_smul m L hL, one_div, mul_inv_rev, inv_inv]
      ring
    have hi : ⟪L⁻¹ • k, L • r⟫_ℝ = ⟪k, r⟫_ℝ := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
    simp only [f, shellIntegrand, hw, hi, Complex.ofReal_mul, energy_inv_smul m L hL,
      Complex.ofReal_inv]
    have hτ' : (L : ℂ) * τ * (L : ℂ)⁻¹ = τ := by
      field_simp
    rw [mul_assoc, show -(↑L * τ) * ((L : ℂ)⁻¹ * (energy (m * L) k : ℂ)) =
      -τ * (energy (m * L) k : ℂ) by
      calc
        _ = -((L : ℂ) * τ * (L : ℂ)⁻¹) * (energy (m * L) k : ℂ) := by ring
        _ = _ := by rw [hτ']]
  simp only [hf, integral_const_mul, Complex.real_smul, Complex.ofReal_pow] at hJ
  change (∫ k, f k) = _
  change _ = ((L : ℂ)^3)⁻¹ * ∫ k, shellIntegrand (m * L) τ r k
  calc
    (∫ k, f k) = ((L : ℂ)^4)⁻¹ * ((L : ℂ) * ∫ k, shellIntegrand (m * L) τ r k) := by
      rw [hJ]
      simp [hL']
    _ = _ := by field_simp


private def gaussianAmplitude (M t : ℝ) (k : E) (s : ℝ) : ℝ :=
  s ^ (-(1/2) : ℝ) * Real.exp (-(energy M k ^ 2 * s) - t^2 / (4 * s))

private def gaussianKernel (M t : ℝ) (r k : E) (s : ℝ) : ℂ :=
  (gaussianAmplitude M t k s : ℂ) * Complex.exp (I * (⟪k, r⟫_ℝ : ℂ))

private def gaussianFactor : ℝ := 1 / ((2 * Real.pi)^4 * (2 * Real.sqrt Real.pi))

private theorem gaussianKernel_norm (M t : ℝ) (r k : E) (s : ℝ) (hs : 0 < s) :
    ‖gaussianKernel M t r k s‖ = gaussianAmplitude M t k s := by
  rw [gaussianKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (show 0 ≤ gaussianAmplitude M t k s by unfold gaussianAmplitude; positivity),
    Complex.norm_exp]
  simp

private theorem gaussianKernel_integral_time (M t : ℝ) (r k : E) :
    (∫ s in Ioi (0 : ℝ), gaussianKernel M t r k s) =
      ↑(∫ s in Ioi (0 : ℝ), gaussianAmplitude M t k s) *
        Complex.exp (I * (⟪k, r⟫_ℝ : ℂ)) := by
  simp only [gaussianKernel, integral_mul_const, integral_complex_ofReal]

private theorem shellIntegrand_eq_gaussian (M : ℝ) {t : ℝ} (ht : 0 < t) (r : E)
    {k : E} (hk : k ≠ 0) :
    shellIntegrand M (t : ℂ) r k =
      (gaussianFactor : ℂ) * ∫ s in Ioi (0 : ℝ), gaussianKernel M t r k s := by
  have h := Omega.gaussian_subordination (energy_pos M hk) ht
  have hscale : shellWeight M k * Real.exp (-t * energy M k) =
      gaussianFactor * ∫ s in Ioi (0 : ℝ), gaussianAmplitude M t k s := by
    calc
      _ = ((2 * Real.pi)^4)⁻¹ * (Real.exp (-t * energy M k) / (2 * energy M k)) := by
        unfold shellWeight
        simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
      _ = _ := by rw [h]; unfold gaussianFactor gaussianAmplitude; ring
  rw [gaussianKernel_integral_time, shellIntegrand, Complex.exp_add, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← mul_assoc, ← Complex.ofReal_mul,
    hscale, Complex.ofReal_mul, mul_assoc]

private theorem gaussianKernel_integrable (M : ℝ) {t : ℝ} (ht : 0 < t) (r : E) :
    Integrable (Function.uncurry (gaussianKernel M t r))
      ((volume : Measure E).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (Function.uncurry (gaussianKernel M t r)) := by
    unfold Function.uncurry gaussianKernel gaussianAmplitude energy
    fun_prop
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [shell_ae_ne_zero] with k hk
    refine ((Omega.integrableOn_gaussian_subordination (energy_pos M hk) ht).mono'
      ?_ ?_ : Integrable (gaussianKernel M t r k) (volume.restrict (Ioi (0 : ℝ))))
    · exact (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      change ‖gaussianKernel M t r k s‖ ≤ gaussianAmplitude M t k s
      exact (gaussianKernel_norm M t r k s hs).le
  · have hfactor : 0 < gaussianFactor := by unfold gaussianFactor; positivity
    -- The absolute integral in the Schwinger parameter comes from the spectral majorant.
    have hdom := ((bulkU5D_integrable M (τ := (t : ℂ)) (by simpa using ht) r).norm).const_mul
      gaussianFactor⁻¹
    refine hdom.congr ?_
    filter_upwards [shell_ae_ne_zero] with k hk
    change gaussianFactor⁻¹ * ‖shellIntegrand M (t : ℂ) r k‖ =
      ∫ s in Ioi (0 : ℝ), ‖gaussianKernel M t r k s‖
    rw [shellIntegrand_eq_gaussian M ht r hk, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hfactor.le, ← mul_assoc, inv_mul_cancel₀ hfactor.ne', one_mul]
    rw [gaussianKernel_integral_time, norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (I * (⟪k, r⟫_ℝ : ℂ)).re = 0 := by simp
    have hnonneg : 0 ≤ ∫ s in Ioi (0 : ℝ), gaussianAmplitude M t k s := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hs : 0 ≤ s) _) (Real.exp_nonneg _)
    rw [hre, Real.exp_zero, mul_one, Real.norm_of_nonneg hnonneg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (gaussianKernel_norm M t r k s hs).symm

private theorem gaussianKernel_integral (M t : ℝ) (r : E) {s : ℝ} (hs : 0 < s) :
    (∫ k, gaussianKernel M t r k s) =
      (((Real.pi ^ 2 * s ^ (-(5 / 2) : ℝ)) *
        Real.exp (-M^2 * s - (‖r‖^2 + t^2) / (4 * s)) : ℝ) : ℂ) := by
  let C : ℝ := s ^ (-(1/2) : ℝ) * Real.exp (-M ^ 2 * s - t ^ 2 / (4 * s))
  have hsplit (k : E) : gaussianKernel M t r k s =
      (C : ℂ) * Complex.exp (-(s : ℂ) * ‖k‖ ^ 2 + I * (⟪r, k⟫_ℝ : ℂ)) := by
    unfold gaussianKernel gaussianAmplitude energy C
    rw [Real.sq_sqrt (by positivity), Complex.exp_add, ← Complex.ofReal_pow,
      ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      real_inner_comm r k]
    push_cast
    rw [show -(((‖k‖ : ℂ)^2 + (M : ℂ)^2) * (s : ℂ)) - (t : ℂ)^2 / (4*s) =
      (-(M : ℂ)^2 * (s : ℂ) - (t : ℂ)^2 / (4*s)) + (-(s : ℂ) * (‖k‖ : ℂ)^2)
      by ring, Complex.exp_add]
    ring
  simp only [hsplit, integral_const_mul]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (by simpa using hs : 0 < (s : ℂ).re)]
  have hpow : (↑Real.pi / (s : ℂ)) ^ (↑(Fintype.card (Fin 4)) / 2 : ℂ) =
      ((Real.pi / s : ℝ) ^ 2 : ℝ) := by
    rw [show (↑(Fintype.card (Fin 4)) / 2 : ℂ) = (2 : ℕ) by norm_num, Complex.cpow_natCast]
    push_cast
    rfl
  have he : Complex.exp (-1 * (‖r‖ : ℂ)^2 / (4 * (s : ℂ))) =
      (Real.exp (-(‖r‖^2) / (4*s)) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    congr 1
    ring
  rw [hpow, Complex.I_sq, he, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_inj]
  unfold C
  rw [div_pow, show (Real.pi ^ 2 / s ^ 2) = Real.pi ^ 2 * s ^ (-2 : ℝ) by
    rw [Real.rpow_neg hs.le, Real.rpow_two, div_eq_mul_inv]]
  have hp : s ^ (-(1/2) : ℝ) * s ^ (-2 : ℝ) = s ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_add hs]
    congr 1 <;> norm_num
  calc
    _ = Real.pi ^ 2 * (s ^ (-(1/2) : ℝ) * s ^ (-2 : ℝ)) *
        (Real.exp (-(‖r‖^2) / (4*s)) * Real.exp (-M^2 * s - t^2 / (4*s))) := by ring
    _ = _ := by
      rw [hp, ← Real.exp_add]
      congr 2
      ring

private abbrev separation (r : E) (τ : ℂ) : ℂ := ((‖r‖^2 : ℝ) : ℂ) + τ^2

private theorem separation_slit (r : E) {τ : ℂ} (hτ : 0 < τ.re) :
    separation r τ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases h : τ.im = 0
  · left
    simp only [separation, pow_two, Complex.add_re, Complex.ofReal_re, Complex.mul_re, h,
      mul_zero, sub_zero]
    positivity
  · right
    simp only [separation, pow_two, Complex.add_im, Complex.ofReal_im, Complex.mul_im, zero_add]
    rw [mul_comm τ.im τ.re, ← two_mul]
    exact mul_ne_zero (by norm_num) (mul_ne_zero hτ.ne' h)

private theorem eq_on_rightHalfPlane {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z | 0 < z.re}) (hg : AnalyticOnNhd ℂ g {z | 0 < z.re})
    (h : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    EqOn f g {z | 0 < z.re} := by
  -- Positive real times above one accumulate at a point in the open half-plane.
  apply hf.eqOn_of_preconnected_of_mem_closure hg
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected
    (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})
  have hcl : (1 : ℝ) ∈ closure (Ioi (1 : ℝ)) := by rw [closure_Ioi]; exact (le_rfl : (1 : ℝ) ≤ 1)
  refine closure_mono ?_ (image_closure_subset_closure_image Complex.continuous_ofReal
    (mem_image_of_mem Complex.ofReal hcl))
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨h t (zero_lt_one.trans ht), by simpa using (show (1 : ℝ) < t from ht).ne'⟩

/-- The elementary massive bulk expression evaluated at a complex separation. -/
def elementary (M : ℝ) (q : ℂ) : ℂ :=
  let root := q ^ (1 / 2 : ℂ)
  Complex.exp (-(M : ℂ) * root) * (1 + (M : ℂ) * root) /
    (8 * (Real.pi : ℂ) ^ 2 * (q * root))

private theorem bulkU5D_real {M t : ℝ} (hM : 0 ≤ M) (ht : 0 < t) (r : E) :
    bulkU5D M (t : ℂ) r = elementary M (separation r t) := by
  let q : ℝ := ‖r‖^2 + t^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hsep : separation r (t : ℂ) = (q : ℂ) := by push_cast [separation, q]; rfl
  have hroot : (q : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt q : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hq.le]
    push_cast
    rfl
  have hnorm : gaussianFactor * Real.pi ^ 2 * (4 * Real.sqrt Real.pi) =
      1 / (8 * Real.pi ^ 2) := by
    unfold gaussianFactor
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 Real.pi_pos).ne']
    <;> ring
  change (∫ k, shellIntegrand M (t : ℂ) r k) = _
  calc
    _ = (gaussianFactor : ℂ) * ∫ k, ∫ s in Ioi (0 : ℝ), gaussianKernel M t r k s := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [shell_ae_ne_zero] with k hk
      exact shellIntegrand_eq_gaussian M ht r hk
    _ = (gaussianFactor : ℂ) * ∫ s in Ioi (0 : ℝ), ∫ k, gaussianKernel M t r k s := by
      rw [integral_integral_swap (gaussianKernel_integrable M ht r)]
    _ = ((gaussianFactor * Real.pi ^ 2 *
        ∫ s in Ioi (0 : ℝ), s ^ (-(5 / 2) : ℝ) *
          Real.exp (-M^2 * s - q / (4 * s)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_mul, mul_assoc]
      apply congrArg ((gaussianFactor : ℂ) * ·)
      rw [← integral_complex_ofReal, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      simpa only [q, Complex.ofReal_mul, mul_assoc] using gaussianKernel_integral M t r hs
    _ = _ := by
      rw [integral_half_integer_schwinger hM hq, elementary, hsep, hroot]
      simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
        ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_pow,
        ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_inj]
      calc
        _ = (gaussianFactor * Real.pi ^ 2 * (4 * Real.sqrt Real.pi)) *
            (Real.exp (-(M * Real.sqrt q)) * (1 + M * Real.sqrt q) / (q * Real.sqrt q)) := by ring
        _ = _ := by rw [hnorm, div_mul_div_comm, one_mul, neg_mul]

/-- The regulated shell integral equals the principal-root elementary expression throughout
the positive real time half-plane. -/
theorem bulkU5D_elementary {M : ℝ} (hM : 0 ≤ M) {τ : ℂ} (hτ : 0 < τ.re) (r : E) :
    bulkU5D M τ r = elementary M (separation r τ) := by
  apply eq_on_rightHalfPlane (f := fun z => bulkU5D M z r)
    (g := fun z => elementary M (separation r z))
  · exact (bulkU5D_differentiableOn M r).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  · intro z hz
    have hs : AnalyticAt ℂ (separation r) z := analyticAt_const.add (analyticAt_id.pow 2)
    have hslit := separation_slit r hz
    have hn := Complex.slitPlane_ne_zero hslit
    have hroot := hs.cpow (analyticAt_const (v := (1 / 2 : ℂ))) hslit
    have hd : 8 * (Real.pi : ℂ) ^ 2 * (separation r z * separation r z ^ (1 / 2 : ℂ)) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hpi))
        (mul_ne_zero hn ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hn))
    unfold elementary
    exact ((((analyticAt_const.mul hroot).cexp).mul
      (analyticAt_const.add (analyticAt_const.mul hroot))).div
      (analyticAt_const.mul (hs.mul hroot)) hd)
  · exact fun t ht => bulkU5D_real hM ht r
  · exact hτ

end FourSpatialMassShell

end Omega
