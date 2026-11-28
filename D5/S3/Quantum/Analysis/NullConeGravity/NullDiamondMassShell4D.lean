/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The regulated momentum integral, closed formulas, and radius scaling. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSchwinger4D
import D5.S3.Analysis.GaussianSubordination
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The regulated mass-shell integral and its continuation from positive Euclidean time. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped InnerProductSpace Topology

namespace NullConeGravity

def energy (M : ℝ) (k : E3) : ℝ := Real.sqrt (‖k‖ ^ 2 + M ^ 2)

/-- The invariant shell density, with value zero at the massless zero momentum. -/
def shellWeight (M : ℝ) (k : E3) : ℝ := 1 / (2 * (2 * Real.pi) ^ 3 * energy M k)

def bulkU (M : ℝ) (τ : ℂ) (r : E3) : ℂ :=
  ∫ k : E3, (shellWeight M k : ℂ) *
    Complex.exp (-τ * (energy M k : ℂ) + I * (⟪k, r⟫_ℝ : ℂ))

private abbrev shellIntegrand (M : ℝ) (τ : ℂ) (r k : E3) : ℂ :=
  (shellWeight M k : ℂ) * Complex.exp (-τ * (energy M k : ℂ) + I * (⟪k, r⟫_ℝ : ℂ))

private theorem norm_le_energy (M : ℝ) (k : E3) : ‖k‖ ≤ energy M k := by
  calc
    ‖k‖ = Real.sqrt (‖k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg k)).symm
    _ ≤ energy M k := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg M))

private theorem energy_nonneg (M : ℝ) (k : E3) : 0 ≤ energy M k :=
  (norm_nonneg k).trans (norm_le_energy M k)

private theorem energy_pos (M : ℝ) {k : E3} (hk : k ≠ 0) : 0 < energy M k :=
  (norm_pos_iff.mpr hk).trans_le (norm_le_energy M k)

private theorem shellWeight_nonneg (M : ℝ) (k : E3) : 0 ≤ shellWeight M k :=
  div_nonneg zero_le_one (mul_nonneg (by positivity) (energy_nonneg M k))

private theorem shellIntegrand_measurable (M : ℝ) (τ : ℂ) (r : E3) :
    Measurable (shellIntegrand M τ r) := by
  unfold shellIntegrand shellWeight energy
  fun_prop

private theorem norm_shellIntegrand (M : ℝ) (τ : ℂ) (r k : E3) :
    ‖shellIntegrand M τ r k‖ = shellWeight M k * Real.exp (-τ.re * energy M k) := by
  rw [shellIntegrand, norm_mul, Complex.norm_real, Real.norm_of_nonneg (shellWeight_nonneg M k),
    Complex.norm_exp]
  congr 2
  simp [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private theorem radial_exp_integrable {d : ℝ} (hd : 0 < d) :
    Integrable (fun k : E3 => Real.exp (-d * ‖k‖)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure E3)
    (f := fun x => Real.exp (-d * x))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2)
    (by norm_num) (by norm_num) hd
  simpa [E3, finrank_euclideanSpace, Real.rpow_two, Real.rpow_one, smul_eq_mul, neg_mul] using h

private theorem radial_inv_exp_integrable {d : ℝ} (hd : 0 < d) :
    Integrable (fun k : E3 => ‖k‖⁻¹ * Real.exp (-d * ‖k‖)) := by
  -- The three-dimensional radial Jacobian cancels the inverse radius at the origin.
  apply (integrable_fun_norm_addHaar (volume : Measure E3)
    (f := fun x => x⁻¹ * Real.exp (-d * x))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
    (by norm_num) (by norm_num) hd
  refine (h.congr_fun ?_ measurableSet_Ioi)
  intro x hx
  simp only [Real.rpow_one, E3, finrank_euclideanSpace, Fintype.card_fin,
    Nat.reduceSub, smul_eq_mul]
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp

private theorem shell_ae_ne_zero : ∀ᵐ k : E3, k ≠ 0 := by
  rw [ae_iff]
  simp

theorem bulkU_integrable (M : ℝ) {τ : ℂ} (hτ : 0 < τ.re) (r : E3) :
    Integrable (fun k : E3 => (shellWeight M k : ℂ) *
      Complex.exp (-τ * (energy M k : ℂ) + I * (⟪k, r⟫_ℝ : ℂ))) := by
  let c : ℝ := (2 * (2 * Real.pi)^3)⁻¹
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
        have hc : ((2 * Real.pi)^3)⁻¹ * (2 : ℝ)⁻¹ = c := by simp only [c, mul_inv_rev]
        rw [hc]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ (energy_pos M hk) (norm_pos_iff.mpr hk)).2 (norm_le_energy M k))
          (show 0 ≤ c by positivity)
      · exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left (norm_le_energy M k) (by linarith))
    _ = _ := mul_assoc _ _ _

private theorem shellWeight_energy_le (M : ℝ) (k : E3) :
    shellWeight M k * energy M k ≤ (2 * (2 * Real.pi)^3)⁻¹ := by
  rcases eq_or_ne (energy M k) 0 with h | h
  · simpa only [h, mul_zero] using (by positivity : 0 ≤ (2 * (2 * Real.pi)^3)⁻¹)
  · simp only [shellWeight, one_div, mul_inv_rev]
    rw [mul_comm (energy M k)⁻¹, mul_assoc, inv_mul_cancel₀ h, mul_one]

theorem bulkU_differentiableOn (M : ℝ) (r : E3) :
    DifferentiableOn ℂ (fun τ => bulkU M τ r) {τ : ℂ | 0 < τ.re} := by
  intro τ hτ
  change 0 < τ.re at hτ
  let c : ℝ := (2 * (2 * Real.pi)^3)⁻¹
  let d : ℝ := τ.re / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let s : Set ℂ := {z | d < z.re}
  have hs : s ∈ 𝓝 τ := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show d < τ.re by dsimp [d]; linarith)
  let F (z : ℂ) (k : E3) := shellIntegrand M z r k
  -- Differentiation supplies the factor of energy needed to cancel the shell denominator.
  let F' (z : ℂ) (k : E3) := -(energy M k : ℂ) * F z k
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) :=
    (shellIntegrand_measurable M z r).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' τ) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ (shellIntegrand_measurable M τ r)
    unfold energy
    fun_prop
  have hbound : ∀ᵐ k : E3, ∀ z ∈ s, ‖F' z k‖ ≤ c * Real.exp (-d * ‖k‖) :=
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
  have hdiff : ∀ᵐ k : E3, ∀ z ∈ s, HasDerivAt (F · k) (F' z k) z :=
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
    (bulkU_integrable M hτ r) hmeas' hbound ((radial_exp_integrable hd).const_mul c)
    hdiff).2.differentiableAt.differentiableWithinAt

private theorem energy_inv_smul (m L : ℝ) (hL : 0 < L) (k : E3) :
    energy m (L⁻¹ • k) = L⁻¹ * energy (m * L) k := by
  simp only [energy, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
  have he : (L⁻¹ * ‖k‖)^2 + m^2 = L⁻¹ ^ 2 * (‖k‖ ^ 2 + (m * L)^2) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg (L⁻¹)), Real.sqrt_sq (inv_nonneg.mpr hL.le)]

/-- The regulator and spatial separation scale together with inverse momentum. -/
theorem bulkU_scale (m L : ℝ) (_hm : 0 ≤ m) (hL : 0 < L)
    {τ : ℂ} (_hτ : 0 < τ.re) (r : E3) :
    bulkU m ((L : ℂ) * τ) (L • r) = ((L : ℂ)^2)⁻¹ * bulkU (m * L) τ r := by
  let f := shellIntegrand m ((L : ℂ) * τ) (L • r)
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hdim : Module.finrank ℝ E3 = 3 := by simp [E3]
  have hJ := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E3) f hL.le
  rw [hdim] at hJ
  have hf (k : E3) : f (L⁻¹ • k) = (L : ℂ) * shellIntegrand (m * L) τ r k := by
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
  change _ = ((L : ℂ)^2)⁻¹ * ∫ k, shellIntegrand (m * L) τ r k
  calc
    (∫ k, f k) = ((L : ℂ)^3)⁻¹ * ((L : ℂ) * ∫ k, shellIntegrand (m * L) τ r k) := by
      rw [hJ]
      simp [hL']
    _ = _ := by field_simp


private def gaussianAmplitude (M t : ℝ) (k : E3) (s : ℝ) : ℝ :=
  s ^ (-(1/2) : ℝ) * Real.exp (-(energy M k ^ 2 * s) - t^2 / (4 * s))

private def gaussianKernel (M t : ℝ) (r k : E3) (s : ℝ) : ℂ :=
  (gaussianAmplitude M t k s : ℂ) * Complex.exp (I * (⟪k, r⟫_ℝ : ℂ))

private def gaussianFactor : ℝ := 1 / ((2 * Real.pi)^3 * (2 * Real.sqrt Real.pi))

private theorem gaussianKernel_norm (M t : ℝ) (r k : E3) (s : ℝ) (hs : 0 < s) :
    ‖gaussianKernel M t r k s‖ = gaussianAmplitude M t k s := by
  rw [gaussianKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (show 0 ≤ gaussianAmplitude M t k s by unfold gaussianAmplitude; positivity),
    Complex.norm_exp]
  simp

private theorem gaussianKernel_integral_time (M t : ℝ) (r k : E3) :
    (∫ s in Ioi (0 : ℝ), gaussianKernel M t r k s) =
      ↑(∫ s in Ioi (0 : ℝ), gaussianAmplitude M t k s) *
        Complex.exp (I * (⟪k, r⟫_ℝ : ℂ)) := by
  simp only [gaussianKernel, integral_mul_const, integral_complex_ofReal]

private theorem shellIntegrand_eq_gaussian (M : ℝ) {t : ℝ} (ht : 0 < t) (r : E3)
    {k : E3} (hk : k ≠ 0) :
    shellIntegrand M (t : ℂ) r k =
      (gaussianFactor : ℂ) * ∫ s in Ioi (0 : ℝ), gaussianKernel M t r k s := by
  have h := Omega.gaussian_subordination (energy_pos M hk) ht
  have hscale : shellWeight M k * Real.exp (-t * energy M k) =
      gaussianFactor * ∫ s in Ioi (0 : ℝ), gaussianAmplitude M t k s := by
    calc
      _ = ((2 * Real.pi)^3)⁻¹ * (Real.exp (-t * energy M k) / (2 * energy M k)) := by
        unfold shellWeight
        simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
      _ = _ := by rw [h]; unfold gaussianFactor gaussianAmplitude; ring
  rw [gaussianKernel_integral_time, shellIntegrand, Complex.exp_add, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← mul_assoc, ← Complex.ofReal_mul,
    hscale, Complex.ofReal_mul, mul_assoc]

private theorem gaussianKernel_integrable (M : ℝ) {t : ℝ} (ht : 0 < t) (r : E3) :
    Integrable (Function.uncurry (gaussianKernel M t r))
      ((volume : Measure E3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
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
    have hdom := ((bulkU_integrable M (τ := (t : ℂ)) (by simpa using ht) r).norm).const_mul
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

private theorem gaussianKernel_integral (M t : ℝ) (r : E3) {s : ℝ} (hs : 0 < s) :
    (∫ k, gaussianKernel M t r k s) =
      (((Real.pi ^ (3/2 : ℝ) * s⁻¹ ^ 2) *
        Real.exp (-M^2 * s - (‖r‖^2 + t^2) / (4 * s)) : ℝ) : ℂ) := by
  let C : ℝ := s ^ (-(1/2) : ℝ) * Real.exp (-M ^ 2 * s - t ^ 2 / (4 * s))
  have hsplit (k : E3) : gaussianKernel M t r k s =
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
  have hpow : (↑Real.pi / (s : ℂ)) ^ (↑(Fintype.card (Fin 3)) / 2 : ℂ) =
      (((Real.pi / s) ^ (3/2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hs.le)]
    norm_num
  have he : Complex.exp (-1 * (‖r‖ : ℂ)^2 / (4 * (s : ℂ))) =
      (Real.exp (-(‖r‖^2) / (4*s)) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    congr 1
    ring
  rw [hpow, Complex.I_sq, he, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_inj]
  unfold C
  rw [Real.div_rpow Real.pi_pos.le hs.le,
    div_eq_mul_inv (Real.pi ^ (3/2 : ℝ)) (s ^ (3/2 : ℝ)), ← Real.rpow_neg hs.le]
  have hp : s ^ (-(1/2) : ℝ) * s ^ (-(3/2) : ℝ) = s⁻¹ ^ 2 := by
    rw [← Real.rpow_add hs, show (-(1/2) + -(3/2) : ℝ) = -2 by norm_num,
      Real.rpow_neg hs.le, Real.rpow_two, inv_pow]
  calc
    _ = Real.pi ^ (3/2 : ℝ) * (s ^ (-(1/2) : ℝ) * s ^ (-(3/2) : ℝ)) *
        (Real.exp (-(‖r‖^2) / (4*s)) * Real.exp (-M^2 * s - t^2 / (4*s))) := by ring
    _ = _ := by
      rw [hp, ← Real.exp_add]
      congr 2
      ring

private theorem gaussianFactor_normalization :
    gaussianFactor * Real.pi ^ (3/2 : ℝ) = 1 / (16 * Real.pi^2) := by
  rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  unfold gaussianFactor
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 Real.pi_pos).ne']
  norm_num

private theorem schwinger_substitution (M : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ), s⁻¹ ^ 2 * Real.exp (-M^2 * s - q / (4 * s))) =
      (4 / q) * schwingerH (M^2 * q / 4) := by
  have hc : 0 < q / 4 := by positivity
  rw [Omega.integral_Ioi_const_div hc, schwingerH, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : s ≠ 0 := ne_of_gt hs
  have hq' := hq.ne'
  simp only [smul_eq_mul]
  rw [show -M^2 * (q / 4 / s) - q / (4 * (q / 4 / s)) = -s - M^2 * q / 4 / s by
    field_simp; ring]
  field_simp

private theorem bulkU_real (M : ℝ) {t : ℝ} (ht : 0 < t) (r : E3) :
    bulkU M (t : ℂ) r =
      (schwingerH (M^2 * (‖r‖^2 + t^2) / 4) : ℂ) /
        (4 * (Real.pi : ℂ)^2 * ((‖r‖^2 + t^2 : ℝ) : ℂ)) := by
  let q : ℝ := ‖r‖^2 + t^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  change (∫ k, shellIntegrand M (t : ℂ) r k) = _
  calc
    _ = (gaussianFactor : ℂ) * ∫ k, ∫ s in Ioi (0 : ℝ), gaussianKernel M t r k s := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [shell_ae_ne_zero] with k hk
      exact shellIntegrand_eq_gaussian M ht r hk
    _ = (gaussianFactor : ℂ) * ∫ s in Ioi (0 : ℝ), ∫ k, gaussianKernel M t r k s := by
      rw [integral_integral_swap (gaussianKernel_integrable M ht r)]
    _ = (gaussianFactor : ℂ) * ((Real.pi ^ (3/2 : ℝ) : ℝ) : ℂ) *
        ↑(∫ s in Ioi (0 : ℝ), s⁻¹ ^ 2 * Real.exp (-M^2 * s - q / (4 * s))) := by
      rw [mul_assoc]
      apply congrArg ((gaussianFactor : ℂ) * ·)
      rw [← integral_complex_ofReal, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      simpa only [q, Complex.ofReal_mul, mul_assoc] using gaussianKernel_integral M t r hs
    _ = _ := by
      rw [← Complex.ofReal_mul, gaussianFactor_normalization, schwinger_substitution M hq]
      change _ = ↑(schwingerH (M^2 * q / 4)) / (4 * (Real.pi : ℂ)^2 * (q : ℂ))
      push_cast
      field_simp
      <;> ring

private abbrev separation (r : E3) (τ : ℂ) : ℂ := ((‖r‖^2 : ℝ) : ℂ) + τ^2

private theorem separation_slit (r : E3) {τ : ℂ} (hτ : 0 < τ.re) :
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

private abbrev masslessFormula (r : E3) (τ : ℂ) : ℂ :=
  1 / (4 * (Real.pi : ℂ)^2 * separation r τ)

private theorem masslessFormula_analytic (r : E3) {τ : ℂ} (hτ : 0 < τ.re) :
    AnalyticAt ℂ (masslessFormula r) τ := by
  have hs : AnalyticAt ℂ (separation r) τ := analyticAt_const.add (analyticAt_id.pow 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact analyticAt_const.div (analyticAt_const.mul hs)
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi))
      (Complex.slitPlane_ne_zero (separation_slit r hτ)))

private theorem massiveFormula_analytic (M : ℝ) (hM : 0 < M) (r : E3) {τ : ℂ}
    (hτ : 0 < τ.re) :
    AnalyticAt ℂ (fun z => bulkDifference M (separation r z)) τ := by
  let g (z : ℂ) := (M : ℂ)^2 * separation r z / 4
  have hga : AnalyticAt ℂ g τ :=
    (analyticAt_const.mul (analyticAt_const.add (analyticAt_id.pow 2))).div_const
  have hslit : g τ ∈ Complex.slitPlane := by
    have hs := Complex.mem_slitPlane_iff.mp (separation_slit r hτ)
    rw [Complex.mem_slitPlane_iff]
    have he : g τ = ((M^2 / 4 : ℝ) : ℂ) * separation r τ := by
      dsimp [g]
      push_cast
      ring
    rw [he]
    rcases hs with h | h
    · left
      rw [Complex.re_ofReal_mul]
      positivity
    · right
      rw [Complex.im_ofReal_mul]
      exact mul_ne_zero (by positivity) h
  have hP : AnalyticAt ℂ besselP (g τ) :=
    (besselP_entire.differentiableOn.analyticOnNhd isOpen_univ) _ (mem_univ _)
  have hB : AnalyticAt ℂ besselB (g τ) :=
    (besselB_entire.differentiableOn.analyticOnNhd isOpen_univ) _ (mem_univ _)
  exact analyticAt_const.mul (((hga.clog hslit).mul (hP.comp hga)).sub (hB.comp hga))

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

private theorem bulkU_analytic (M : ℝ) (r : E3) :
    AnalyticOnNhd ℂ (fun z => bulkU M z r) {z | 0 < z.re} :=
  (bulkU_differentiableOn M r).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem bulkU_zero {τ : ℂ} (hτ : 0 < τ.re) (r : E3) :
    bulkU 0 τ r = 1/(4*(Real.pi : ℂ)^2*(((‖r‖^2 : ℝ) : ℂ) + τ^2)) := by
  apply eq_on_rightHalfPlane (bulkU_analytic 0 r) (fun _ hz => masslessFormula_analytic r hz) _ hτ
  intro t ht
  have hzero : schwingerH 0 = 1 := by
    simpa [schwingerH] using integral_exp_neg_Ioi_zero
  rw [bulkU_real 0 ht r]
  simp [hzero, masslessFormula, separation]

theorem bulkU_difference {M : ℝ} (hM : 0 < M)
    {τ : ℂ} (hτ : 0 < τ.re) (r : E3) :
    bulkU M τ r - bulkU 0 τ r = bulkDifference M (((‖r‖^2 : ℝ) : ℂ) + τ^2) := by
  apply eq_on_rightHalfPlane ((bulkU_analytic M r).sub (bulkU_analytic 0 r))
    (fun _ hz => massiveFormula_analytic M hM r hz) _ hτ
  intro t ht
  let q : ℝ := ‖r‖^2 + t^2
  let z : ℝ := M^2 * q / 4
  have hq : 0 < q := by dsimp [q]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht' : 0 < (t : ℂ).re := by simpa using ht
  change bulkU M (t : ℂ) r - bulkU 0 (t : ℂ) r = bulkDifference M (separation r (t : ℂ))
  rw [bulkU_real M ht r, bulkU_zero ht' r]
  change (schwingerH z : ℂ) / (4 * (Real.pi : ℂ)^2 * (q : ℂ)) -
    1 / (4 * (Real.pi : ℂ)^2 * separation r (t : ℂ)) =
      bulkDifference M (separation r (t : ℂ))
  have eq : separation r (t : ℂ) = (q : ℂ) := by simp only [q, Complex.ofReal_add,
    Complex.ofReal_pow, separation]
  rw [eq, schwingerH_eq_series hz, Complex.ofReal_log hz.le, bulkDifference,
    show (M : ℂ)^2 * (q : ℂ) / 4 = (z : ℂ) by simp [z]]
  have hzc : (z : ℂ) = (M : ℂ)^2 * (q : ℂ) / 4 := by simp [z]
  field_simp
  ring_nf
  rw [hzc]
  ring

end NullConeGravity
