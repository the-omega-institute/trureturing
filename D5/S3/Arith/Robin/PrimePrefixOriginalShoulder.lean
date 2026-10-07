/- GID: D5/S3/Arith/Robin/PrimePrefixOriginalShoulder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixOriginalShoulder
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The complete literal original shoulder has a strict uniform half-gamma supremum reserve. -/

import D5.S3.Arith.Robin.PrimePrefixMacroProfile
import D5.S3.Arith.Robin.PrimePrefixOriginalA
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
The actual two-piece A endpoint is reused from PrimePrefixOriginalA. The
literal normalizedZeta and macro-profile endpoint are reused from
PrimePrefixMacroProfile. Its consumed Bose/Gamma supplier bodies preserve
the classical Gamma/Bose attribution and the FermiMellin attribution to
David Sanftenberg (2026), Apache-2.0. The complete log-exponential and tail
FTC bodies retain their Mertens.Gamma and PrimePrefixOriginalA provenance.

The original shoulder is compared on its entire positive integration axis.
The complete comparison is a unit-mass exponential average. Positive mass
outside the scalar equality layer supplies the additional fixed reserve
from actual-prefix theory section 447, strengthened by its half-gamma
simplification in section 451. No full Robin pairing or RH endpoint
is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
namespace D5.S3.Arith.Robin.PrimePrefixOriginalShoulder
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
open D5.S3.Arith.Robin.PrimePrefixMacroProfile

/-- The original Euler amplitude. -/
def eulerAmplitude : ℝ := Real.exp Real.eulerMascheroniConstant
/-- The actual excess coefficient C-1. -/
def slopeExcess : ℝ := eulerAmplitude - 1
/-- The original complete two-piece constant. -/
def originalA : ℝ :=
  (∫ v in (0 : ℝ)..1, (actualPhi v * (1 - Real.exp (-v)) - v) / v ^ 2) +
  (∫ v : ℝ in Ioi 1, actualPhi v * (1 - Real.exp (-v)) / v ^ 2 - eulerAmplitude / v)
/-- The actual normalized-zeta shoulder kernel. -/
def shoulderBeta (u : ℝ) : ℝ := (1 / normalizedZeta u - 1) / u
/-- The original complete shoulder. -/
def originalShoulder (t : ℝ) : ℝ :=
  originalA - slopeExcess * (Real.log t + Real.eulerMascheroniConstant) +
    eulerAmplitude * ∫ u : ℝ in Ioi 0, Real.exp (-t * u) * shoulderBeta u
/-- The original positive fixed reserve. -/
def shoulderDelta : ℝ := (2 * Real.log 2 - 1) / 6
/-- The comparison's classical scalar barrier. -/
def lowerBarrier (r : ℝ) : ℝ := r * (1 + Real.log ((1 + r) / (2 * r)))
/-- The extra mass paid outside the scalar equality layer. -/
def extraReserve (r : ℝ) : ℝ := r * Real.exp (-2 / r) * (Real.log 2 - 1 / 2)

private def expTail (x : ℝ) : ℝ := ∫ y : ℝ in Ioi x, Real.exp (-y) / y
private def comparison (x : ℝ) : ℝ :=
  slopeExcess * (Real.log (x / 2) + Real.eulerMascheroniConstant) +
    eulerAmplitude * Real.exp x * expTail x
private def pointBarrier (y : ℝ) : ℝ :=
  slopeExcess * (Real.log (y / 2) + Real.eulerMascheroniConstant) + 1 / y
private def weightedGap (y : ℝ) : ℝ :=
  Real.exp (-y) * (pointBarrier y - lowerBarrier slopeExcess)

private theorem amplitude_pos : 0 < eulerAmplitude := Real.exp_pos _
private theorem excess_gt_third : (1 / 3 : ℝ) < slopeExcess := by
  have hgamma := Real.one_half_lt_eulerMascheroniConstant
  have hexp := Real.add_one_le_exp Real.eulerMascheroniConstant
  dsimp [slopeExcess, eulerAmplitude]
  linarith
private theorem excess_pos : 0 < slopeExcess := by linarith [excess_gt_third]
private theorem amplitude_eq_one_add_excess : eulerAmplitude = 1 + slopeExcess := by
  unfold slopeExcess
  ring

namespace Bose

noncomputable section

private def boseIntegrand (u t : ℝ) : ℝ :=
  t ^ u / (Real.exp t - 1)

private def fermiIntegrand (u t : ℝ) : ℝ :=
  t ^ u / (Real.exp t + 1)

private def doubledBoseIntegrand (u t : ℝ) : ℝ :=
  t ^ u / (Real.exp (2 * t) - 1)

private theorem psi_le_one_add {t : ℝ} (ht : 0 < t) :
    t / (1 - Real.exp (-t)) ≤ 1 + t := by
  have hden : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hmul : (1 + t) * Real.exp (-t) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos t)).2
    simpa only [one_mul, add_comm] using Real.add_one_le_exp t
  apply (div_le_iff₀ hden).2
  nlinarith

private theorem bose_eq_gamma_weighted_psi {u t : ℝ} (ht : 0 < t) :
    boseIntegrand u t =
      (Real.exp (-t) * t ^ (u - 1)) *
        (t / (1 - Real.exp (-t))) := by
  have hden : Real.exp t - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).ne'
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hneg : 1 - (Real.exp t)⁻¹ ≠ 0 := by
    have h : 0 < 1 - Real.exp (-t) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    simpa only [Real.exp_neg] using h.ne'
  unfold boseIntegrand
  rw [Real.rpow_sub ht u 1, Real.rpow_one, Real.exp_neg]
  field_simp [ht.ne', hexp, hden, hneg]
  <;> ring

private theorem integrable_bose {u : ℝ} (hu : 0 < u) :
    IntegrableOn (boseIntegrand u) (Ioi (0 : ℝ)) := by
  have hnext : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ u) (Ioi (0 : ℝ)) := by
    simpa only [add_sub_cancel_right] using
      (Real.GammaIntegral_convergent (s := u + 1) (by linarith))
  have hmajor : IntegrableOn
      (fun t : ℝ =>
        Real.exp (-t) * t ^ (u - 1) + Real.exp (-t) * t ^ u)
      (Ioi (0 : ℝ)) :=
    (Real.GammaIntegral_convergent hu).add hnext
  have hcont : ContinuousOn (boseIntegrand u) (Ioi (0 : ℝ)) := by
    unfold boseIntegrand
    exact (continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt ht))).div
      (Real.continuous_exp.sub continuous_const).continuousOn
      (fun t ht =>
        (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).ne')
  apply hmajor.mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hnonneg : 0 ≤ boseIntegrand u t := by
    unfold boseIntegrand
    exact div_nonneg (Real.rpow_nonneg ht.le u)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    bose_eq_gamma_weighted_psi ht]
  have hp : t ^ (u - 1) * t = t ^ u := by
    calc
      t ^ (u - 1) * t = t ^ ((u - 1) + 1) := by
        rw [Real.rpow_add ht, Real.rpow_one]
      _ = t ^ u := by congr 1 <;> ring
  calc
    (Real.exp (-t) * t ^ (u - 1)) *
        (t / (1 - Real.exp (-t))) ≤
        (Real.exp (-t) * t ^ (u - 1)) * (1 + t) :=
      mul_le_mul_of_nonneg_left (psi_le_one_add ht)
        (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _))
    _ = Real.exp (-t) * t ^ (u - 1) +
        Real.exp (-t) * (t ^ (u - 1) * t) := by ring
    _ = Real.exp (-t) * t ^ (u - 1) +
        Real.exp (-t) * t ^ u := by rw [hp]

private theorem fermi_complex_point (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (((1 + u : ℝ) : ℂ) - 1) /
        ((Real.exp (1 * t) : ℂ) + 1) =
      (fermiIntegrand u t : ℂ) := by
  have hexponent : ((1 + u : ℝ) : ℂ) - 1 = (u : ℂ) := by
    push_cast
    ring
  rw [hexponent, one_mul, ← Complex.ofReal_cpow ht.le]
  simp only [fermiIntegrand, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_one]

private theorem fermi_real_supplier {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fermiIntegrand u) (Ioi (0 : ℝ)) ∧
      (∫ t : ℝ in Ioi 0, fermiIntegrand u t) =
        Real.Gamma (1 + u) * (1 - (2 : ℝ) ^ (-u)) *
          (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
  have hs : 0 < (((1 + u : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hs1 : ((1 + u : ℝ) : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hr
    linarith
  have hC := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable
    1 (by norm_num) ((1 + u : ℝ) : ℂ) hs
  have hformula :=
    D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_eq_of_ne_one
      1 (by norm_num) ((1 + u : ℝ) : ℂ) hs hs1
  have hpower :
      (2 : ℂ) ^ (1 - ((1 + u : ℝ) : ℂ)) =
        (((2 : ℝ) ^ (-u) : ℝ) : ℂ) := by
    have he : 1 - ((1 + u : ℝ) : ℂ) = ((-u : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he]
    have hc := (Complex.ofReal_cpow
      (by norm_num : 0 ≤ (2 : ℝ)) (-u)).symm
    norm_num at hc
    simpa only [Complex.ofReal_neg] using hc
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at hformula
  rw [Complex.Gamma_ofReal, hpower] at hformula
  constructor
  · apply hC.re.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp := congrArg Complex.re (fermi_complex_point u ht)
    simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using hp
  · calc
      (∫ t : ℝ in Ioi 0, fermiIntegrand u t) =
          ∫ t : ℝ in Ioi 0,
            ((t : ℂ) ^ (((1 + u : ℝ) : ℂ) - 1) /
              ((Real.exp (1 * t) : ℂ) + 1)).re := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have hp := congrArg Complex.re (fermi_complex_point u ht)
        simpa only [Complex.ofReal_re] using hp.symm
      _ = (∫ t : ℝ in Ioi 0,
            (t : ℂ) ^ (((1 + u : ℝ) : ℂ) - 1) /
              ((Real.exp (1 * t) : ℂ) + 1)).re :=
        integral_re hC
      _ = Real.Gamma (1 + u) * (1 - (2 : ℝ) ^ (-u)) *
          (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
        simp only [one_mul]
        rw [hformula]
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
          Complex.sub_im, Complex.one_re, Complex.one_im,
          Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_mul, sub_zero, zero_sub, add_zero, sub_self]

private theorem doubled_bose_point (u : ℝ) {t : ℝ} (ht : 0 < t) :
    doubledBoseIntegrand u t =
      ((2 : ℝ) ^ u)⁻¹ * boseIntegrand u (2 * t) := by
  have hp : (2 : ℝ) ^ u ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) u).ne'
  have hd : Real.exp (2 * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))).ne'
  unfold doubledBoseIntegrand boseIntegrand
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le]
  field_simp [hp, hd]
  <;> ring

private theorem integrable_doubled_bose {u : ℝ} (hu : 0 < u) :
    IntegrableOn (doubledBoseIntegrand u) (Ioi (0 : ℝ)) := by
  have hcomp : IntegrableOn
      (fun t : ℝ => boseIntegrand u (2 * t)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (boseIntegrand u) 0 (a := 2) (by norm_num)).2
    simpa only [mul_zero] using integrable_bose hu
  apply (hcomp.const_mul (((2 : ℝ) ^ u)⁻¹)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (doubled_bose_point u ht).symm

private theorem integral_doubled_bose {u : ℝ} (hu : 0 < u) :
    2 * (∫ t : ℝ in Ioi 0, doubledBoseIntegrand u t) =
      (2 : ℝ) ^ (-u) *
        (∫ t : ℝ in Ioi 0, boseIntegrand u t) := by
  have hscale :
      (∫ t : ℝ in Ioi 0, boseIntegrand u (2 * t)) =
        (2 : ℝ)⁻¹ * (∫ t : ℝ in Ioi 0, boseIntegrand u t) := by
    simpa only [mul_zero, smul_eq_mul] using
      (integral_comp_mul_left_Ioi
        (boseIntegrand u) 0 (b := 2) (by norm_num))
  have hpoint :
      (∫ t : ℝ in Ioi 0, doubledBoseIntegrand u t) =
        ((2 : ℝ) ^ u)⁻¹ *
          (∫ t : ℝ in Ioi 0, boseIntegrand u (2 * t)) := by
    calc
      _ = ∫ t : ℝ in Ioi 0,
            ((2 : ℝ) ^ u)⁻¹ * boseIntegrand u (2 * t) := by
        exact setIntegral_congr_fun measurableSet_Ioi
          (fun t ht => doubled_bose_point u ht)
      _ = _ := integral_const_mul _ _
  rw [hpoint, hscale, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  <;> ring

private theorem fermi_eq_bose_sub_doubled (u : ℝ) {t : ℝ} (ht : 0 < t) :
    fermiIntegrand u t =
      boseIntegrand u t - 2 * doubledBoseIntegrand u t := by
  have he : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hminus : Real.exp t - 1 ≠ 0 := (sub_pos.mpr he).ne'
  have hplus : Real.exp t + 1 ≠ 0 := by positivity
  have hfactor :
      Real.exp t * Real.exp t - 1 =
        (Real.exp t - 1) * (Real.exp t + 1) := by ring
  unfold fermiIntegrand boseIntegrand doubledBoseIntegrand
  rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add, hfactor]
  field_simp [hminus, hplus]
  <;> ring

private theorem integral_fermi_eq_bose_factor {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Ioi 0, fermiIntegrand u t) =
      (1 - (2 : ℝ) ^ (-u)) *
        (∫ t : ℝ in Ioi 0, boseIntegrand u t) := by
  have hb := integrable_bose hu
  have hd := integrable_doubled_bose hu
  calc
    _ = ∫ t : ℝ in Ioi 0,
          (boseIntegrand u t - 2 * doubledBoseIntegrand u t) := by
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => fermi_eq_bose_sub_doubled u ht)
    _ = (∫ t : ℝ in Ioi 0, boseIntegrand u t) -
          2 * (∫ t : ℝ in Ioi 0, doubledBoseIntegrand u t) := by
      rw [integral_sub hb (hd.const_mul 2), integral_const_mul]
    _ = _ := by rw [integral_doubled_bose hu] <;> ring

private theorem actual_prefix_bose_normalization {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => t ^ u / (Real.exp t - 1))
        (Ioi (0 : ℝ)) ∧
      (∫ t : ℝ in Ioi 0, t ^ u / (Real.exp t - 1)) =
        Real.Gamma (1 + u) *
          (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
  have hb := integrable_bose hu
  have hf := fermi_real_supplier hu
  have hfactor_pos : 0 < 1 - (2 : ℝ) ^ (-u) := by
    apply sub_pos.mpr
    apply (Real.rpow_lt_one_iff_of_pos
      (by norm_num : (0 : ℝ) < 2)).2
    exact Or.inl ⟨by norm_num, by linarith⟩
  have heq :
      (1 - (2 : ℝ) ^ (-u)) *
          (∫ t : ℝ in Ioi 0, boseIntegrand u t) =
        (1 - (2 : ℝ) ^ (-u)) *
          (Real.Gamma (1 + u) *
            (riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
    calc
      _ = ∫ t : ℝ in Ioi 0, fermiIntegrand u t :=
        (integral_fermi_eq_bose_factor hu).symm
      _ = Real.Gamma (1 + u) * (1 - (2 : ℝ) ^ (-u)) *
          (riemannZeta ((1 + u : ℝ) : ℂ)).re := hf.2
      _ = _ := by ring
  constructor
  · exact hb
  · exact mul_left_cancel₀ hfactor_pos.ne' heq

private theorem actual_prefix_q_integral_binding {u : ℝ} (hu : 0 < u) :
    IntegrableOn
        (fun t : ℝ =>
          (t / (1 - Real.exp (-t))) *
            (Real.exp (-t) * t ^ (u - 1) / Real.Gamma u))
        (Ioi (0 : ℝ)) ∧
      u * (riemannZeta ((1 + u : ℝ) : ℂ)).re =
        ∫ t : ℝ in Ioi 0,
          (t / (1 - Real.exp (-t))) *
            (Real.exp (-t) * t ^ (u - 1) / Real.Gamma u) := by
  have hb := actual_prefix_bose_normalization hu
  have hg : Real.Gamma u ≠ 0 := (Real.Gamma_pos_of_pos hu).ne'
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (t / (1 - Real.exp (-t))) *
          (Real.exp (-t) * t ^ (u - 1) / Real.Gamma u) =
        (Real.Gamma u)⁻¹ * boseIntegrand u t := by
    rw [bose_eq_gamma_weighted_psi ht]
    simp only [div_eq_mul_inv]
    ring
  constructor
  · apply (hb.1.const_mul ((Real.Gamma u)⁻¹)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hpoint t ht).symm
  · symm
    calc
      _ = ∫ t : ℝ in Ioi 0,
            (Real.Gamma u)⁻¹ * boseIntegrand u t := by
        exact setIntegral_congr_fun measurableSet_Ioi hpoint
      _ = (Real.Gamma u)⁻¹ *
          (∫ t : ℝ in Ioi 0, boseIntegrand u t) :=
        integral_const_mul _ _
      _ = (Real.Gamma u)⁻¹ *
          (Real.Gamma (1 + u) *
            (riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
        unfold boseIntegrand
        rw [hb.2]
      _ = u * (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
        rw [show 1 + u = u + 1 by ring, Real.Gamma_add_one hu.ne']
        field_simp [hg]
        <;> ring


end

end Bose

namespace GammaBound

private def density (u t : ℝ) : ℝ :=
  Real.exp (-t) * t ^ (u - 1) / Real.Gamma u

private def psi (t : ℝ) : ℝ :=
  t / (1 - Real.exp (-t))

private theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) :
    0 < 1 - Real.exp (-t) := by
  apply sub_pos.mpr
  calc
    Real.exp (-t) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

private theorem density_pos {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    0 < density u t := by
  unfold density
  exact div_pos
    (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _))
    (Real.Gamma_pos_of_pos hu)

private theorem density_integrable {u : ℝ} (hu : 0 < u) :
    IntegrableOn (density u) (Ioi (0 : ℝ)) := by
  exact (Real.GammaIntegral_convergent hu).div_const (Real.Gamma u)

private theorem density_mass {u : ℝ} (hu : 0 < u) :
    (∫ t in Ioi (0 : ℝ), density u t) = 1 := by
  unfold density
  rw [integral_div, ← Real.Gamma_eq_integral hu]
  exact div_self (Real.Gamma_pos_of_pos hu).ne'

private theorem moment_model {u t : ℝ} (ht : 0 < t) :
    t * density u t =
      Real.exp (-t) * t ^ ((u + 1) - 1) / Real.Gamma u := by
  have hr : t ^ ((u + 1) - 1) = t ^ (u - 1) * t := by
    rw [show (u + 1) - 1 = (u - 1) + 1 by ring,
      Real.rpow_add_one ht.ne']
  rw [density, hr]
  ring

private theorem density_moment_integrable {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => t * density u t) (Ioi (0 : ℝ)) := by
  have hu1 : 0 < u + 1 := by linarith
  refine Integrable.congr
    ((Real.GammaIntegral_convergent hu1).div_const (Real.Gamma u)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t ht
  exact (moment_model (mem_Ioi.mp ht)).symm

private theorem density_firstMoment {u : ℝ} (hu : 0 < u) :
    (∫ t in Ioi (0 : ℝ), t * density u t) = u := by
  have hu1 : 0 < u + 1 := by linarith
  calc
    (∫ t in Ioi (0 : ℝ), t * density u t) =
        ∫ t in Ioi (0 : ℝ),
          Real.exp (-t) * t ^ ((u + 1) - 1) / Real.Gamma u := by
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => moment_model (mem_Ioi.mp ht))
    _ = Real.Gamma (u + 1) / Real.Gamma u := by
      rw [integral_div, ← Real.Gamma_eq_integral hu1]
    _ = u := by
      rw [Real.Gamma_add_one hu.ne', mul_div_assoc,
        div_self (Real.Gamma_pos_of_pos hu).ne', mul_one]

private theorem psi_le_one_add {t : ℝ} (ht : 0 < t) : psi t ≤ 1 + t := by
  have hd := one_sub_exp_pos ht
  have he := Real.add_one_le_exp t
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-t)).le
  have hex : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold psi
  apply (div_le_iff₀ hd).2
  nlinarith [hm, hex]

end GammaBound

private lemma log_integrable :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private theorem integrableOn_expTail_kernel {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun w : ℝ => Real.exp (-w) / w) (Ioi v) := by
  apply Integrable.mono' ((integrableOn_exp_neg_Ioi v).div_const v)
  · exact ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with w hw
    have hwpos : 0 < w := hv.trans hw
    simp only [norm_div, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-w)),
      abs_of_pos hwpos]
    exact div_le_div_of_nonneg_left (Real.exp_pos (-w)).le hv hw.le

private theorem log_tail_hasDerivAt {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun x : ℝ => Real.log x * Real.exp (-x))
      (Real.exp (-w) / w - Real.log w * Real.exp (-w)) w := by
  have h := (Real.hasDerivAt_log hw.ne').mul ((hasDerivAt_id w).neg.exp)
  apply h.congr_deriv
  dsimp
  simp only [div_eq_mul_inv]
  ring

private theorem log_tail_value {v : ℝ} (hv : 0 < v) :
    (∫ w : ℝ in Ioi v, Real.log w * Real.exp (-w)) =
      Real.exp (-v) * Real.log v + expTail v := by
  have hl : IntegrableOn (fun w : ℝ => Real.log w * Real.exp (-w)) (Ioi v) :=
    log_integrable.mono_set (Ioi_subset_Ioi hv.le)
  have hd : IntegrableOn
      (fun w : ℝ => Real.exp (-w) / w - Real.log w * Real.exp (-w)) (Ioi v) :=
    (integrableOn_expTail_kernel hv).sub hl
  have hder : ∀ w ∈ Ioi v, HasDerivAt (fun x : ℝ => Real.log x * Real.exp (-x))
      (Real.exp (-w) / w - Real.log w * Real.exp (-w)) w :=
    fun w hw => log_tail_hasDerivAt (hv.trans hw)
  have ht : Tendsto (fun w : ℝ => Real.log w * Real.exp (-w)) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hder hd hl
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (log_tail_hasDerivAt hv).continuousAt.continuousWithinAt hder hd ht
  rw [integral_sub (integrableOn_expTail_kernel hv) hl] at h
  dsimp only [expTail]
  linarith

private theorem q_pos {u : ℝ} (hu : 0 < u) : 0 < normalizedZeta u := by
  exact mul_pos hu (riemannZeta_re_pos_of_one_lt (by linarith))

private theorem q_upper {u : ℝ} (hu : 0 < u) : normalizedZeta u ≤ 1 + u := by
  have hbind := Bose.actual_prefix_q_integral_binding hu
  have hi : IntegrableOn
      (fun t : ℝ => GammaBound.psi t * GammaBound.density u t) (Ioi 0) := by
    simpa only [GammaBound.psi, GammaBound.density] using hbind.1
  have hd := GammaBound.density_integrable hu
  have hm := GammaBound.density_moment_integrable hu
  have hcmp := setIntegral_mono_on hi (hd.add hm) measurableSet_Ioi
    (fun t ht => show GammaBound.psi t * GammaBound.density u t ≤
      GammaBound.density u t + t * GammaBound.density u t from by
        have hp := GammaBound.psi_le_one_add ht
        have hdpos := GammaBound.density_pos hu ht
        nlinarith)
  simp only [Pi.add_apply] at hcmp
  rw [integral_add hd hm, GammaBound.density_mass hu,
    GammaBound.density_firstMoment hu] at hcmp
  have hq : normalizedZeta u =
      ∫ t : ℝ in Ioi 0, GammaBound.psi t * GammaBound.density u t := by
    simpa only [normalizedZeta, GammaBound.psi, GammaBound.density] using hbind.2
  rw [hq]
  exact hcmp

private theorem q_secant {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b - a) / 2 < normalizedZeta b - normalizedZeta a := by
  have hb := ha.trans hab
  have hqa := q_pos ha
  have hqb := q_pos hb
  have hden := mul_pos hqa hqb
  have hdrop := D5.S3.Arith.Robin.PrimePrefixMacroProfile.result ha hab
  have hleft : Real.exp Real.eulerMascheroniConstant * (b-a) /
      (2 * normalizedZeta a * normalizedZeta b) =
      (Real.exp Real.eulerMascheroniConstant * ((b-a)/2)) /
        (normalizedZeta a * normalizedZeta b) := by
    field_simp [hqa.ne', hqb.ne'] <;> ring
  have hright : macroProfile a - macroProfile b =
      Real.exp Real.eulerMascheroniConstant * (normalizedZeta b - normalizedZeta a) /
        (normalizedZeta a * normalizedZeta b) := by
    unfold macroProfile
    field_simp [hqa.ne', hqb.ne'] <;> ring
  rw [hleft, hright] at hdrop
  have hscaled := (div_lt_div_iff_of_pos_right hden).1 hdrop
  nlinarith [Real.exp_pos Real.eulerMascheroniConstant]

private theorem q_right_limit : Tendsto normalizedZeta (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have harg : Tendsto (fun u : ℝ => ((1+u : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hca : Continuous (fun u : ℝ => ((1+u : ℝ) : ℂ)) := by fun_prop
      have htn : Tendsto (fun u : ℝ => ((1+u : ℝ) : ℂ)) (𝓝 0) (𝓝 1) := by
        simpa only [add_zero, Complex.ofReal_one] using hca.tendsto 0
      exact htn.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change 0 < u at hu
      apply Set.mem_compl_singleton_iff.mpr
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.one_re] at hre
      linarith
  have hc := riemannZeta_residue_one.comp harg
  have hr := (Complex.continuous_re.tendsto (1 : ℂ)).comp hc
  have hpoint (u : ℝ) :
      ((((1+u : ℝ) : ℂ)-1) * riemannZeta ((1+u : ℝ) : ℂ)).re =
        normalizedZeta u := by
    simp only [normalizedZeta, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      sub_self, zero_mul, sub_zero]
    ring
  simpa only [Function.comp_def, Complex.one_re, hpoint] using hr

private theorem q_lower {u : ℝ} (hu : 0 < u) : 1 + u/2 ≤ normalizedZeta u := by
  have hl : Tendsto (fun a : ℝ => normalizedZeta a + (u-a)/2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 + u/2)) := by
    have ha : Tendsto (fun a : ℝ => (u-a)/2) (𝓝[>] (0 : ℝ)) (𝓝 (u/2)) := by
      have hi : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa only [sub_zero] using (tendsto_const_nhds (x := u)).sub hi |>.div_const 2
    exact q_right_limit.add ha
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hu)] with a ha hau
  have hs := q_secant ha hau
  linarith

private theorem q_continuousOn : ContinuousOn normalizedZeta (Ioi (0 : ℝ)) := by
  intro u hu
  change 0 < u at hu
  have hs : ((1+u : ℝ) : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    linarith
  have harg : ContinuousAt (fun v : ℝ => ((1+v : ℝ) : ℂ)) u := by fun_prop
  have hc : ContinuousAt (fun v : ℝ => riemannZeta ((1+v : ℝ) : ℂ)) u :=
    (differentiableAt_riemannZeta hs).continuousAt.comp
      (f := fun v : ℝ => ((1+v : ℝ) : ℂ)) harg
  have hr := Complex.continuous_re.continuousAt.comp hc
  exact (continuous_id.continuousAt.mul hr).continuousWithinAt

private theorem beta_bounds {u : ℝ} (hu : 0 < u) :
    |shoulderBeta u| ≤ 1 ∧ shoulderBeta u ≤ -1 / (u+2) := by
  have hq := q_pos hu
  have hlow := q_lower hu
  have hhigh := q_upper hu
  have hq1 : 1 ≤ normalizedZeta u := by linarith
  have hden := mul_pos hq hu
  have hid : shoulderBeta u =
      (1-normalizedZeta u) / (normalizedZeta u * u) := by
    unfold shoulderBeta
    field_simp [hq.ne', hu.ne'] <;> ring
  rw [hid]
  constructor
  · rw [abs_div, abs_of_pos hden, abs_of_nonpos (sub_nonpos.mpr hq1)]
    apply (div_le_iff₀ hden).2
    nlinarith
  · apply (div_le_div_iff₀ hden (show 0 < u+2 by linarith)).2
    nlinarith

private theorem beta_continuousOn : ContinuousOn shoulderBeta (Ioi (0 : ℝ)) := by
  unfold shoulderBeta
  exact ((continuousOn_const.div q_continuousOn
    (fun u hu => (q_pos hu).ne')).sub continuousOn_const).div continuousOn_id
      (fun u hu => hu.ne')

private theorem shoulder_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => Real.exp (-t*u) * shoulderBeta u) (Ioi 0) := by
  have he := integrableOn_exp_mul_Ioi (show -t < 0 by linarith) 0
  have hc : ContinuousOn (fun u : ℝ => Real.exp (-t*u) * shoulderBeta u) (Ioi 0) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-t*u))).continuousOn.mul
      beta_continuousOn
  apply Integrable.mono' he (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-t*u)), Real.norm_eq_abs]
  have hb := (beta_bounds hu).1
  nlinarith [Real.exp_pos (-t*u)]

private def comparisonKernel (t u : ℝ) : ℝ := Real.exp (-t*u)/(u+2)

private theorem comparisonKernel_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (comparisonKernel t) (Ioi (0 : ℝ)) := by
  have he := (integrableOn_exp_mul_Ioi (show -t < 0 by linarith) 0).const_mul (1/2 : ℝ)
  have hc : ContinuousOn (comparisonKernel t) (Ioi (0 : ℝ)) := by
    unfold comparisonKernel
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-t*u))).continuousOn.div
      (continuousOn_id.add continuousOn_const) (fun u hu => (by change 0 < u at hu; linarith : u+2 ≠ 0))
  apply Integrable.mono' he (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  change 0 < u at hu
  change |Real.exp (-t*u)/(u+2)| ≤ (1/2 : ℝ)*Real.exp (-t*u)
  rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le (by linarith))]
  change Real.exp (-t*u)/(u+2) ≤ (1/2 : ℝ)*Real.exp (-t*u)
  have h := div_le_div_of_nonneg_left (Real.exp_pos (-t*u)).le
    (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ u+2 by linarith)
  linarith

private theorem comparisonKernel_tail_binding {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, comparisonKernel t u) = Real.exp (2*t)*expTail (2*t) := by
  let f : ℝ → ℝ := fun u => t*(u+2)
  let g : ℝ → ℝ := fun y => Real.exp (-y)/y
  have htwopos : 0 < 2*t := by positivity
  have hpoint (u : ℝ) (hu : 0 ≤ u) :
      (g ∘ f) u * t = Real.exp (-(2*t)) * comparisonKernel t u := by
    dsimp [g, f, comparisonKernel]
    rw [show -(t*(u+2)) = -(2*t)+(-t*u) by ring, Real.exp_add]
    field_simp [ht.ne', show u+2 ≠ 0 by linarith] <;> ring
  have hfcont : ContinuousOn f (Ici (0 : ℝ)) := by dsimp [f]; fun_prop
  have hftop : Tendsto f atTop atTop := by
    exact (tendsto_atTop_add_const_right _ 2 tendsto_id).const_mul_atTop ht
  have hfder : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt f t (Ioi u) u := by
    intro u _
    have hd : HasDerivAt (fun v : ℝ => t*(v+2)) t u := by
      convert! (hasDerivAt_const_mul t).comp u ((hasDerivAt_id u).add_const 2) using 1 <;>
        simp [Function.comp_def]
    exact hd.hasDerivWithinAt
  have hgcont : ContinuousOn g (f '' Ioi (0 : ℝ)) := by
    have hgc : ContinuousOn g (Ioi (0 : ℝ)) := by
      dsimp [g]
      exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
        (fun y hy => hy.ne')
    apply hgc.mono
    rintro y ⟨u, hu, rfl⟩
    change 0 < u at hu
    change 0 < t*(u+2)
    positivity
  have hgint : IntegrableOn g (f '' Ici (0 : ℝ)) := by
    apply ((integrableOn_Ici_iff_integrableOn_Ioi).2
      (integrableOn_expTail_kernel htwopos)).mono_set
    rintro y ⟨u, hu, rfl⟩
    change 0 ≤ u at hu
    change 2*t ≤ t*(u+2)
    nlinarith
  have hcint : IntegrableOn (fun u => (g ∘ f) u * t) (Ici (0 : ℝ)) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi).2
    apply IntegrableOn.congr_fun
      ((comparisonKernel_integrable ht).const_mul (Real.exp (-(2*t))))
    · intro u hu
      exact (hpoint u hu.le).symm
    · exact measurableSet_Ioi
  have hsub := integral_comp_mul_deriv_Ioi hfcont hftop hfder hgcont hgint hcint
  have hleft : (∫ u : ℝ in Ioi 0, (g ∘ f) u * t) =
      Real.exp (-(2*t)) * (∫ u : ℝ in Ioi 0, comparisonKernel t u) := by
    calc
      _ = ∫ u : ℝ in Ioi 0, Real.exp (-(2*t))*comparisonKernel t u :=
        setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpoint u hu.le)
      _ = _ := integral_const_mul _ _
  rw [hleft] at hsub
  have hs : Real.exp (-(2*t)) * (∫ u : ℝ in Ioi 0, comparisonKernel t u) =
      expTail (2*t) := by
    simpa only [f, g, Function.comp_def, zero_add, mul_comm, expTail] using hsub
  have he : Real.exp (2*t)*Real.exp (-(2*t)) = 1 := by rw [← Real.exp_add]; simp
  calc
    (∫ u : ℝ in Ioi 0, comparisonKernel t u) =
        Real.exp (2*t)*(Real.exp (-(2*t))*(∫ u : ℝ in Ioi 0, comparisonKernel t u)) := by
          rw [← mul_assoc, he, one_mul]
    _ = _ := by rw [hs]

private theorem shoulder_le_comparison {t : ℝ} (ht : 0 < t) :
    originalShoulder t ≤ originalA - comparison (2*t) := by
  have hs := shoulder_integrable ht
  have hc := comparisonKernel_integrable ht
  have hcmp : (∫ u : ℝ in Ioi 0, Real.exp (-t*u)*shoulderBeta u) ≤
      -(∫ u : ℝ in Ioi 0, comparisonKernel t u) := by
    rw [← integral_neg]
    apply setIntegral_mono_on hs hc.neg measurableSet_Ioi
    intro u hu
    have h := mul_le_mul_of_nonneg_left (beta_bounds hu).2 (Real.exp_pos (-t*u)).le
    simpa only [comparisonKernel, Pi.neg_apply, neg_div, mul_neg, mul_one_div] using h
  rw [comparisonKernel_tail_binding ht] at hcmp
  have hlog : Real.log ((2*t)/2) = Real.log t := by congr 1; ring
  unfold originalShoulder comparison
  rw [hlog]
  nlinarith [amplitude_pos]

private theorem weightedPoint_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => Real.exp (-y)*pointBarrier y) (Ioi x) := by
  have hl := log_integrable.mono_set (Ioi_subset_Ioi hx.le)
  have hc := (integrableOn_exp_neg_Ioi x).const_mul
    (Real.eulerMascheroniConstant - Real.log 2)
  have hi := ((hl.add hc).const_mul slopeExcess).add (integrableOn_expTail_kernel hx)
  apply IntegrableOn.congr_fun hi
  · intro y hy
    dsimp only [Pi.add_apply, pointBarrier]
    rw [Real.log_div (hx.trans hy).ne' (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  · exact measurableSet_Ioi

private theorem weightedPoint_value {x : ℝ} (hx : 0 < x) :
    (∫ y : ℝ in Ioi x, Real.exp (-y)*pointBarrier y) =
      Real.exp (-x)*(slopeExcess*(Real.log (x/2)+Real.eulerMascheroniConstant)) +
        eulerAmplitude*expTail x := by
  have hl := log_integrable.mono_set (Ioi_subset_Ioi hx.le)
  have hc := (integrableOn_exp_neg_Ioi x).const_mul
    (Real.eulerMascheroniConstant - Real.log 2)
  have hsum : IntegrableOn (fun y : ℝ => Real.log y*Real.exp (-y) +
      (Real.eulerMascheroniConstant-Real.log 2)*Real.exp (-y)) (Ioi x) := by
    convert! hl.add hc using 1
  have hs := hsum.const_mul slopeExcess
  have he := integrableOn_expTail_kernel hx
  calc
    _ = ∫ y : ℝ in Ioi x,
        slopeExcess*(Real.log y*Real.exp (-y) +
          (Real.eulerMascheroniConstant-Real.log 2)*Real.exp (-y)) + Real.exp (-y)/y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only [pointBarrier]
      rw [Real.log_div (hx.trans hy).ne' (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    _ = slopeExcess*((∫ y : ℝ in Ioi x, Real.log y*Real.exp (-y)) +
          (Real.eulerMascheroniConstant-Real.log 2)*(∫ y : ℝ in Ioi x, Real.exp (-y))) +
        expTail x := by
      rw [integral_add hs he, integral_const_mul]
      rw [integral_add hl hc, integral_const_mul]
      rfl
    _ = _ := by
      rw [log_tail_value hx, integral_exp_neg_Ioi,
        Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0), amplitude_eq_one_add_excess]
      ring

private theorem comparison_exp_average {x : ℝ} (hx : 0 < x) :
    comparison x = Real.exp x*
      (∫ y : ℝ in Ioi x, Real.exp (-y)*pointBarrier y) := by
  have he : Real.exp x*Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [weightedPoint_value hx]
  calc
    _ = (Real.exp x*Real.exp (-x))*
        (slopeExcess*(Real.log (x/2)+Real.eulerMascheroniConstant)) +
        eulerAmplitude*Real.exp x*expTail x := by
      unfold comparison
      rw [he]
      ring
    _ = _ := by ring

private theorem point_gap_eq {y : ℝ} (hy : 0 < y) :
    pointBarrier y - lowerBarrier slopeExcess =
      slopeExcess*(Real.log (slopeExcess*y) + 1/(slopeExcess*y) - 1) := by
  have hk := excess_pos
  have hk1 : 0 < 1+slopeExcess := by positivity
  have hlog : Real.log (1+slopeExcess) = Real.eulerMascheroniConstant := by
    rw [← amplitude_eq_one_add_excess]
    exact Real.log_exp _
  unfold pointBarrier lowerBarrier
  rw [Real.log_div hy.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hk1.ne' (mul_pos (by norm_num : (0 : ℝ) < 2) hk).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hk.ne', hlog,
    Real.log_mul hk.ne' hy.ne']
  field_simp [hk.ne', hy.ne'] <;> ring

private theorem point_gap_nonneg {y : ℝ} (hy : 0 < y) :
    0 ≤ pointBarrier y - lowerBarrier slopeExcess := by
  rw [point_gap_eq hy]
  have hlog := Real.one_sub_inv_le_log_of_pos (mul_pos excess_pos hy)
  have hscalar : 0 ≤ Real.log (slopeExcess*y)+1/(slopeExcess*y)-1 := by
    simpa only [one_div] using (show 0 ≤ Real.log (slopeExcess*y) +
      (slopeExcess*y)⁻¹ - 1 from by linarith)
  exact mul_nonneg excess_pos.le hscalar

private theorem point_gap_on_tail {x y : ℝ} (hx : 0 < x)
    (hy : x+2/slopeExcess < y) :
    slopeExcess*(Real.log 2-1/2) ≤ pointBarrier y-lowerBarrier slopeExcess := by
  have hk := excess_pos
  have hcancel : slopeExcess*(2/slopeExcess) = (2 : ℝ) := mul_div_cancel₀ 2 hk.ne'
  have hm := mul_lt_mul_of_pos_left hy hk
  have hxy : 0 < y := by
    have hp : 0 < 2/slopeExcess := div_pos (by norm_num) hk
    linarith
  have hr : (2 : ℝ) ≤ slopeExcess*y := by nlinarith [mul_pos hk hx]
  have hrpos : 0 < slopeExcess*y := mul_pos hk hxy
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < (slopeExcess*y)/2 by positivity)
  have heq : ((slopeExcess*y)/2)⁻¹ = 2/(slopeExcess*y) := by field_simp [hrpos.ne']
  rw [heq, Real.log_div hrpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hl
  have htwo : 2/(slopeExcess*y) = 2*(1/(slopeExcess*y)) := by ring
  rw [htwo] at hl
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hr
  have hf : Real.log 2-1/2 ≤ Real.log (slopeExcess*y)+1/(slopeExcess*y)-1 := by
    linarith
  rw [point_gap_eq hxy]
  exact mul_le_mul_of_nonneg_left hf hk.le

private theorem weightedGap_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn weightedGap (Ioi x) := by
  have hi := (weightedPoint_integrable hx).sub
    ((integrableOn_exp_neg_Ioi x).const_mul (lowerBarrier slopeExcess))
  apply IntegrableOn.congr_fun hi
  · intro y _
    dsimp only [weightedGap, Pi.sub_apply]
    ring
  · exact measurableSet_Ioi

private theorem comparison_gap_average {x : ℝ} (hx : 0 < x) :
    comparison x-lowerBarrier slopeExcess =
      Real.exp x*(∫ y : ℝ in Ioi x, weightedGap y) := by
  have hp := weightedPoint_integrable hx
  have hc := (integrableOn_exp_neg_Ioi x).const_mul (lowerBarrier slopeExcess)
  have hi : (∫ y : ℝ in Ioi x, weightedGap y) =
      (∫ y : ℝ in Ioi x, Real.exp (-y)*pointBarrier y) -
        lowerBarrier slopeExcess*Real.exp (-x) := by
    calc
      _ = ∫ y : ℝ in Ioi x,
          Real.exp (-y)*pointBarrier y - lowerBarrier slopeExcess*Real.exp (-y) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y _
            unfold weightedGap
            ring
      _ = _ := by rw [integral_sub hp hc, integral_const_mul, integral_exp_neg_Ioi]
  have he : Real.exp x*Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hcval : Real.exp x*(lowerBarrier slopeExcess*Real.exp (-x)) =
      lowerBarrier slopeExcess := by
    calc
      _ = lowerBarrier slopeExcess*(Real.exp x*Real.exp (-x)) := by ring
      _ = _ := by rw [he, mul_one]
  rw [hi, comparison_exp_average hx, mul_sub, hcval]

private theorem comparison_extra_mass {x : ℝ} (hx : 0 < x) :
    lowerBarrier slopeExcess+extraReserve slopeExcess ≤ comparison x := by
  let z : ℝ := x+2/slopeExcess
  let q : ℝ := slopeExcess*(Real.log 2-1/2)
  have hzx : x < z := by
    dsimp [z]
    exact lt_add_of_pos_right _ (div_pos (by norm_num) excess_pos)
  have hsub : Ioi z ⊆ Ioi x := Ioi_subset_Ioi hzx.le
  have hg := weightedGap_integrable hx
  have hn : 0 ≤ᵐ[volume.restrict (Ioi x)] weightedGap := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact mul_nonneg (Real.exp_pos (-y)).le (point_gap_nonneg (hx.trans hy))
  have hs : (∫ y : ℝ in Ioi z, weightedGap y) ≤
      ∫ y : ℝ in Ioi x, weightedGap y := setIntegral_mono_set hg hn hsub.eventuallyLE
  have hq : q*Real.exp (-z) ≤ ∫ y : ℝ in Ioi z, weightedGap y := by
    rw [← integral_exp_neg_Ioi z, ← integral_const_mul]
    apply setIntegral_mono_on ((integrableOn_exp_neg_Ioi z).const_mul q)
      (hg.mono_set hsub) measurableSet_Ioi
    intro y hy
    have hp := point_gap_on_tail hx (show x+2/slopeExcess < y from hy)
    unfold weightedGap
    dsimp [q]
    nlinarith [Real.exp_pos (-y)]
  have hscaled := mul_le_mul_of_nonneg_left (hq.trans hs) (Real.exp_pos x).le
  have he : Real.exp x*Real.exp (-z) = Real.exp (-2/slopeExcess) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [z]
    ring
  have hmass : Real.exp x*(q*Real.exp (-z)) = extraReserve slopeExcess := by
    calc
      _ = q*(Real.exp x*Real.exp (-z)) := by ring
      _ = _ := by rw [he]; dsimp [q, extraReserve]; ring
  rw [hmass, ← comparison_gap_average hx] at hscaled
  linarith

private theorem delta_pos : 0 < shoulderDelta := by
  have h := Real.log_lt_sub_one_of_pos (show 0 < (1/2 : ℝ) by norm_num)
    (show (1/2 : ℝ) ≠ 1 by norm_num)
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_one] at h
  dsimp [shoulderDelta]
  linarith

private theorem excess_gt_half : (1/2 : ℝ) < slopeExcess := by
  have hgamma := Real.one_half_lt_eulerMascheroniConstant
  have hexp := Real.add_one_le_exp Real.eulerMascheroniConstant
  dsimp [slopeExcess, eulerAmplitude]
  linarith

private theorem lowerBarrier_twoThirds : (2/3 : ℝ) < lowerBarrier slopeExcess := by
  have hk := excess_pos
  have hd : 0 < 1+slopeExcess := by linarith
  have hr : 0 < (1+slopeExcess)/(2*slopeExcess) := div_pos hd (by positivity)
  have hl := Real.one_sub_inv_le_log_of_pos hr
  have heq : ((1+slopeExcess)/(2*slopeExcess))⁻¹ =
      2*slopeExcess/(1+slopeExcess) := by
    field_simp [hk.ne', hd.ne']
  rw [heq] at hl
  have hs := mul_le_mul_of_nonneg_left hl hk.le
  have hid : slopeExcess*(2-2*slopeExcess/(1+slopeExcess)) =
      2*slopeExcess/(1+slopeExcess) := by
    field_simp [hd.ne'] <;> ring
  have hlow : 2*slopeExcess/(1+slopeExcess) ≤ lowerBarrier slopeExcess := by
    unfold lowerBarrier
    linarith
  have hthird : (2/3 : ℝ) < 2*slopeExcess/(1+slopeExcess) := by
    apply (lt_div_iff₀ hd).2
    nlinarith [excess_gt_half]
  exact hthird.trans_le hlow

private theorem lowerBarrier_reserve : 1/2+shoulderDelta < lowerBarrier slopeExcess := by
  have hlog := Real.log_lt_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  have htarget : 1/2+shoulderDelta < (2/3 : ℝ) := by
    dsimp [shoulderDelta]
    linarith
  exact htarget.trans lowerBarrier_twoThirds

private theorem extraReserve_halfGamma :
    (3/2 : ℝ)*shoulderDelta*Real.exp (-4) < extraReserve slopeExcess := by
  have hk := excess_pos
  have hd := delta_pos
  have hq : 0 < Real.log 2-1/2 := by
    dsimp [shoulderDelta] at hd
    linarith
  have hden : 2/slopeExcess < 4 := by
    apply (div_lt_iff₀ hk).2
    nlinarith [excess_gt_half]
  have he : Real.exp (-4) < Real.exp (-2/slopeExcess) :=
    Real.exp_lt_exp.mpr (by rw [neg_div]; linarith)
  have hcoef : (3/2 : ℝ)*shoulderDelta < slopeExcess*(Real.log 2-1/2) := by
    have hm := mul_lt_mul_of_pos_right excess_gt_half hq
    dsimp [shoulderDelta]
    nlinarith [hm]
  have hfirst := mul_lt_mul_of_pos_right hcoef (Real.exp_pos (-4))
  have hsecond := mul_lt_mul_of_pos_left he (mul_pos hk hq)
  unfold extraReserve
  nlinarith

private theorem extraReserve_reserve :
    shoulderDelta*Real.exp (-6) < extraReserve slopeExcess := by
  have hd := delta_pos
  have he : Real.exp (-6) < Real.exp (-4) := Real.exp_lt_exp.mpr (by norm_num)
  have hfirst := mul_lt_mul_of_pos_left he hd
  have hsecond : shoulderDelta*Real.exp (-4) <
      (3/2 : ℝ)*shoulderDelta*Real.exp (-4) := by
    nlinarith [mul_pos hd (Real.exp_pos (-4))]
  exact (hfirst.trans hsecond).trans extraReserve_halfGamma

private theorem originalA_lt_half : originalA < 1/2 := by
  simpa only [originalA, eulerAmplitude] using
    D5.S3.Arith.Robin.PrimePrefixOriginalA.result.2.2

private theorem shoulder_fixed_barrier {t : ℝ} (ht : 0 < t) :
    originalShoulder t ≤ originalA-lowerBarrier slopeExcess-extraReserve slopeExcess := by
  have hs := shoulder_le_comparison ht
  have hc := comparison_extra_mass (show 0 < 2*t by positivity)
  linarith

private theorem barrier_halfGamma :
    originalA-lowerBarrier slopeExcess-extraReserve slopeExcess <
      -(1/6 : ℝ)-(3/2 : ℝ)*shoulderDelta*Real.exp (-4) := by
  nlinarith [originalA_lt_half, lowerBarrier_twoThirds, extraReserve_halfGamma]

private theorem barrier_lt_target :
    originalA-lowerBarrier slopeExcess-extraReserve slopeExcess <
      -shoulderDelta*(1+Real.exp (-6)) := by
  nlinarith [originalA_lt_half, lowerBarrier_reserve, extraReserve_reserve]

/-- The complete original shoulder has an explicit strict supremum reserve. -/
theorem result :
    0 < shoulderDelta ∧
    (∀ t : ℝ, 0 < t →
      IntegrableOn (fun u : ℝ => Real.exp (-t*u)*shoulderBeta u) (Ioi 0)) ∧
    (∀ t : ℝ, 0 < t → originalShoulder t ≤
      originalA-lowerBarrier slopeExcess-extraReserve slopeExcess) ∧
    sSup (originalShoulder '' Ioi (0 : ℝ)) <
      -(1/6 : ℝ)-(3/2 : ℝ)*shoulderDelta*Real.exp (-4) ∧
    sSup (originalShoulder '' Ioi (0 : ℝ)) <
      -shoulderDelta*(1+Real.exp (-6)) := by
  refine ⟨delta_pos, fun t ht => shoulder_integrable ht,
    fun t ht => shoulder_fixed_barrier ht, ?_⟩
  have hn : (originalShoulder '' Ioi (0 : ℝ)).Nonempty :=
    ⟨originalShoulder 1, ⟨1, by norm_num, rfl⟩⟩
  have hs : sSup (originalShoulder '' Ioi (0 : ℝ)) ≤
      originalA-lowerBarrier slopeExcess-extraReserve slopeExcess := by
    apply csSup_le hn
    rintro _ ⟨t, ht, rfl⟩
    exact shoulder_fixed_barrier ht
  exact ⟨hs.trans_lt barrier_halfGamma, hs.trans_lt barrier_lt_target⟩

end D5.S3.Arith.Robin.PrimePrefixOriginalShoulder
