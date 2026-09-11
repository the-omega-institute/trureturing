/- GID: D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint
   mirror-E: none(waiver:actual-Gamma-graph-realization-remains-separate)
   anchors: []
   utility: none
   digest: Bound the genuine logarithmic Gamma endpoint singularity and integrate its complete squared envelope without an integrability premise. -/

import D5.S3.Weil.ZetaBridge.WeilGammaLogarithmicSeed
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Full residual integration at the Gamma endpoints

The actual Gamma image in the preceding owner contains log(1-exp(-d)).
Its square must be integrated rather than discarded at a numerical endpoint.
This module bounds that singular factor, proves the exact exponential-coordinate
square-envelope integral, and derives integrability and the full tail estimate
for bounded complex coefficient functions. No target residual bound or
integrability of the singular expression is an input.

The physical substitution t=exp(-x), the complete Gamma-action realization,
the Taylor-cell certificate and the prolate graph-norm comparison are paper
bridges in the existing RH theory volume. They are not conclusions of this
module. In particular this source does not assert a small residual/gap ratio.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilGammaResidualEndpoint

open MeasureTheory Set Filter
open scoped Topology

/-- The actual Gamma endpoint logarithm is controlled by the endpoint distance.
The distance d may be larger than t, so multiple boundary contributions can
use a common local distance without removing any singular coefficient. -/
theorem gamma_endpoint_log_bound {d t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (htd : t ≤ d) :
    |Real.log (1 - Real.exp (-d))| ≤ 1 - Real.log t := by
  have hd : 0 < d := ht.trans_le htd
  have hpt : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hpd : 0 < 1 - Real.exp (-d) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hupper : 1 - Real.exp (-d) < 1 := by linarith [Real.exp_pos (-d)]
  have hlogneg := Real.log_neg hpd hupper
  have hprod : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
  have hcomp : t * Real.exp (-t) ≤ 1 - Real.exp (-t) := by
    rw [hprod] at he
    nlinarith
  have hlog := Real.log_le_log (mul_pos ht (Real.exp_pos (-t))) hcomp
  rw [Real.log_mul ht.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hmono : 1 - Real.exp (-t) ≤ 1 - Real.exp (-d) := by
    have he := Real.exp_le_exp.mpr (show -d ≤ -t by linarith)
    linarith
  have hlogmono := Real.log_le_log hpt hmono
  rw [abs_of_neg hlogneg]
  linarith

private def primitive (A B x : ℝ) : ℝ :=
  -Real.exp (-x) * ((A + B * x) ^ 2 + 2 * B * (A + B * x) + 2 * B ^ 2)

private theorem primitive_derivative (A B x : ℝ) :
    HasDerivAt (primitive A B) (Real.exp (-x) * (A + B * x) ^ 2) x := by
  have he := (((hasDerivAt_id x).neg).exp).neg
  have hl := ((hasDerivAt_id x).const_mul B).const_add A
  have hp := ((hl.pow 2).add (hl.const_mul (2 * B))).add_const (2 * B ^ 2)
  convert! he.mul hp using 1
  simp
  ring

private theorem primitive_limit (A B : ℝ) :
    Tendsto (primitive A B) atTop (𝓝 0) := by
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).const_mul
    (A ^ 2 + 2 * A * B + 2 * B ^ 2)
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul
    (2 * A * B + 2 * B ^ 2)
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (B ^ 2)
  have hh := ((h0.add h1).add h2).neg
  simp only [mul_zero, add_zero, neg_zero] at hh
  convert hh using 1
  funext x
  dsimp [primitive]
  ring

/-- Exact full exponential-coordinate squared envelope, including integrability.
There is no terminal integration cutoff. A and B may have either sign. -/
theorem exponential_affine_square_tail (A B T : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * (A + B * x) ^ 2) (Ioi T) ∧
    (∫ x : ℝ in Ioi T, Real.exp (-x) * (A + B * x) ^ 2) =
      Real.exp (-T) * ((A + B * T) ^ 2 + 2 * B * (A + B * T) + 2 * B ^ 2) := by
  have hd : ∀ x ∈ Ici T,
      HasDerivAt (primitive A B) (Real.exp (-x) * (A + B * x) ^ 2) x :=
    fun x _ => primitive_derivative A B x
  have hn : ∀ x ∈ Ioi T, 0 ≤ Real.exp (-x) * (A + B * x) ^ 2 :=
    fun x _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hn (primitive_limit A B)
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi (primitive_limit A B)]
  dsimp [primitive]
  ring

/-- The actual log(1-exp(-distance)) expression has a complete integrable
squared tail in logarithmic endpoint coordinates. Bounds on the independently
specified coefficient functions and distances imply the error bound; neither
integrability nor a bound on the assembled residual is assumed. -/
theorem gamma_logarithmic_endpoint_tail
    (f g : ℝ → ℂ) (distance : ℝ → ℝ) (A B T : ℝ)
    (hf : Measurable f) (hg : Measurable g) (hd : Measurable distance)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hfbound : ∀ x ∈ Ioi T, ‖f x‖ ≤ A)
    (hgbound : ∀ x ∈ Ioi T, ‖g x‖ ≤ B)
    (hdistance : ∀ x ∈ Ioi T, Real.exp (-x) ≤ distance x) :
    let R := fun x => f x + (Real.log (1 - Real.exp (-distance x)) : ℂ) * g x
    IntegrableOn (fun x : ℝ => Real.exp (-x) * ‖R x‖ ^ 2) (Ioi T) ∧
    (∫ x : ℝ in Ioi T, Real.exp (-x) * ‖R x‖ ^ 2) ≤
      Real.exp (-T) *
        ((A + B + B * T) ^ 2 + 2 * B * (A + B + B * T) + 2 * B ^ 2) := by
  let R := fun x => f x + (Real.log (1 - Real.exp (-distance x)) : ℂ) * g x
  change IntegrableOn (fun x : ℝ => Real.exp (-x) * ‖R x‖ ^ 2) (Ioi T) ∧ _
  have hm : Measurable (fun x : ℝ => Real.exp (-x) * ‖R x‖ ^ 2) := by
    dsimp [R]
    fun_prop
  have hn (x : ℝ) : 0 ≤ Real.exp (-x) * ‖R x‖ ^ 2 := by positivity
  have hb (x : ℝ) (hx : x ∈ Ioi T) :
      Real.exp (-x) * ‖R x‖ ^ 2 ≤ Real.exp (-x) * (A + B + B * x) ^ 2 := by
    have hx0 : 0 ≤ x := hT.trans (le_of_lt hx)
    have hh := gamma_endpoint_log_bound (Real.exp_pos (-x))
      (Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)) (hdistance x hx)
    rw [Real.log_exp] at hh
    have hl : ‖(Real.log (1 - Real.exp (-distance x)) : ℂ)‖ ≤ 1 + x := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, sub_neg_eq_add] using hh
    have hR : ‖R x‖ ≤ A + B + B * x := by
      calc
        _ ≤ ‖f x‖ + ‖(Real.log (1 - Real.exp (-distance x)) : ℂ) * g x‖ := norm_add_le _ _
        _ = ‖f x‖ + ‖(Real.log (1 - Real.exp (-distance x)) : ℂ)‖ * ‖g x‖ := by rw [norm_mul]
        _ ≤ A + (1 + x) * B := add_le_add (hfbound x hx)
          (mul_le_mul hl (hgbound x hx) (norm_nonneg _) (by linarith))
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hR) (Real.exp_pos _).le
  have majorant := exponential_affine_square_tail (A + B) B T
  have hi : IntegrableOn (fun x : ℝ => Real.exp (-x) * ‖R x‖ ^ 2) (Ioi T) := by
    apply majorant.1.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
    exact hb x hx
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : ℝ in Ioi T, Real.exp (-x) * (A + B + B * x) ^ 2 := by
      apply integral_mono_ae hi majorant.1
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hb x hx
    _ = _ := majorant.2

#print axioms gamma_endpoint_log_bound
#print axioms exponential_affine_square_tail
#print axioms gamma_logarithmic_endpoint_tail

end D5.S3.Weil.ZetaBridge.WeilGammaResidualEndpoint
