/- GID: D5/S3/Arith/Robin/PrimePrefixMacroProfile
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixMacroProfile
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A complete Bose integral and Gamma crossing give a quantitative strict decrease of the literal prime-prefix macro profile. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import D5.S3.Weil.ZetaBridge.FermiMellin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
The macro profile of a complete prime prefix is exp(gamma)/(u*zeta(1+u)).
A complete Bose integral binding and a Gamma density comparison prove an
explicit strict decrease bound for this literal profile on the positive axis.

The Fermi Mellin supplier is reused from D5.S3.Weil.ZetaBridge.FermiMellin,
attributed there to David Sanftenberg (2026), Apache-2.0; see
Library/Weil/sanftenberg2026fermi.md. The Bose/Gamma integral representations
are classical (NIST DLMF 25.5.1 and 5.9.1). The proof uses the Gamma likelihood
ratio crossing with chi(t)=t/(1-exp(-t))-t/2 to quantify the decrease.
The statement concerns this macro profile; it does not assert a finite-prefix
Euler error estimate or the sign of a complete Robin pairing.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.PrimePrefixMacroProfile

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

namespace GammaComparison

private def density (u t : ℝ) : ℝ :=
  Real.exp (-t) * t ^ (u - 1) / Real.Gamma u

private def psi (t : ℝ) : ℝ :=
  t / (1 - Real.exp (-t))

private def chi (t : ℝ) : ℝ :=
  psi t - t / 2

private def expectation (u : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), psi t * density u t

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

private theorem density_continuousOn (u : ℝ) :
    ContinuousOn (density u) (Ioi (0 : ℝ)) := by
  have he : ContinuousOn (fun t : ℝ => Real.exp (-t)) (Ioi (0 : ℝ)) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn
  have hp : ContinuousOn (fun t : ℝ => t ^ (u - 1)) (Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const
      (fun t ht => Or.inl (mem_Ioi.mp ht).ne')
  exact (he.mul hp).div_const (Real.Gamma u)

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

private theorem one_le_psi {t : ℝ} (ht : 0 < t) : 1 ≤ psi t := by
  have hd := one_sub_exp_pos ht
  unfold psi
  apply (le_div_iff₀ hd).2
  have he := Real.add_one_le_exp (-t)
  nlinarith

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

private theorem psi_continuousOn : ContinuousOn psi (Ioi (0 : ℝ)) := by
  have he : ContinuousOn (fun t : ℝ => Real.exp (-t)) (Ioi (0 : ℝ)) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn
  exact continuousOn_id.div (continuousOn_const.sub he)
    (fun t ht => (one_sub_exp_pos (mem_Ioi.mp ht)).ne')

private theorem psi_density_integrable {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => psi t * density u t) (Ioi (0 : ℝ)) := by
  refine ((density_integrable hu).add (density_moment_integrable hu)).mono'
    ((psi_continuousOn.mul (density_continuousOn u)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t ht
  have ht0 : 0 < t := mem_Ioi.mp ht
  have hd : 0 ≤ density u t := (density_pos hu ht0).le
  have hp : 0 ≤ psi t := le_trans zero_le_one (one_le_psi ht0)
  change ‖psi t * density u t‖ ≤ density u t + t * density u t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hd)]
  calc
    psi t * density u t ≤ (1 + t) * density u t :=
      mul_le_mul_of_nonneg_right (psi_le_one_add ht0) hd
    _ = density u t + t * density u t := by ring

private theorem chi_continuousOn : ContinuousOn chi (Ioi (0 : ℝ)) := by
  exact psi_continuousOn.sub (continuousOn_id.div_const (2 : ℝ))

private theorem chi_density_integrable {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => chi t * density u t) (Ioi (0 : ℝ)) := by
  refine ((psi_density_integrable hu).sub
    ((density_moment_integrable hu).div_const (2 : ℝ))).congr_fun
      ?_ measurableSet_Ioi
  intro t ht
  change psi t * density u t - (t * density u t) / 2 = chi t * density u t
  unfold chi
  ring

private theorem chi_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt chi
      (Real.exp (-t) * (Real.sinh t - t) / (1 - Real.exp (-t)) ^ 2) t := by
  have hd0 := one_sub_exp_pos ht
  have he : HasDerivAt (fun w : ℝ => Real.exp (-w)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hd : HasDerivAt chi
      ((1 - Real.exp (-t) - t * Real.exp (-t)) /
        (1 - Real.exp (-t)) ^ 2 - 1 / 2) t := by
    change HasDerivAt (fun w : ℝ =>
      w / (1 - Real.exp (-w)) - w / 2)
        ((1 - Real.exp (-t) - t * Real.exp (-t)) /
          (1 - Real.exp (-t)) ^ 2 - 1 / 2) t
    simpa only [one_mul, neg_neg, id_eq, Pi.sub_def] using!
      ((hasDerivAt_id t).fun_div (he.const_sub 1) hd0.ne').sub
        ((hasDerivAt_id t).div_const (2 : ℝ))
  have hex : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hcoef :
      (1 - Real.exp (-t) - t * Real.exp (-t)) /
          (1 - Real.exp (-t)) ^ 2 - 1 / 2 =
        Real.exp (-t) * (Real.sinh t - t) /
          (1 - Real.exp (-t)) ^ 2 := by
    rw [Real.sinh_eq]
    field_simp [hd0.ne'] <;> nlinarith [hex]
  rw [hcoef] at hd
  exact hd

private theorem chi_strictMonoOn : StrictMonoOn chi (Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) chi_continuousOn ?_
  intro t ht
  have ht0 : 0 < t := by
    simpa only [interior_Ioi, mem_Ioi] using ht
  rw [(chi_hasDerivAt ht0).deriv]
  exact div_pos
    (mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.self_lt_sinh_iff.mpr ht0)))
    (sq_pos_of_pos (one_sub_exp_pos ht0))

private def crossing (a b : ℝ) : ℝ :=
  Real.exp (Real.log (Real.Gamma b / Real.Gamma a) / (b - a))

private theorem crossing_pos (a b : ℝ) : 0 < crossing a b :=
  Real.exp_pos _

private theorem crossing_rpow {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    crossing a b ^ (b - a) = Real.Gamma b / Real.Gamma a := by
  have hb : 0 < b := lt_trans ha hab
  have hratio : 0 < Real.Gamma b / Real.Gamma a :=
    div_pos (Real.Gamma_pos_of_pos hb) (Real.Gamma_pos_of_pos ha)
  have hdiff : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  unfold crossing
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    div_mul_cancel₀ _ hdiff, Real.exp_log hratio]

private theorem crossing_factor_one {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Real.Gamma a / Real.Gamma b) * crossing a b ^ (b - a) = 1 := by
  have hb : 0 < b := lt_trans ha hab
  rw [crossing_rpow ha hab]
  field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.Gamma_pos_of_pos hb).ne']

private theorem density_factor {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    density b t = density a t *
      ((Real.Gamma a / Real.Gamma b) * t ^ (b - a)) := by
  have hp : t ^ (b - 1) = t ^ (a - 1) * t ^ (b - a) := by
    rw [show b - 1 = (a - 1) + (b - a) by ring, Real.rpow_add ht]
  unfold density
  rw [hp]
  field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.Gamma_pos_of_pos hb).ne']

private theorem density_lt_before_crossing {a b t : ℝ}
    (ha : 0 < a) (hab : a < b) (ht : 0 < t) (htc : t < crossing a b) :
    density b t < density a t := by
  have hb : 0 < b := lt_trans ha hab
  have hratio : 0 < Real.Gamma a / Real.Gamma b :=
    div_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb)
  have hp := Real.rpow_lt_rpow ht.le htc (sub_pos.mpr hab)
  have hf : (Real.Gamma a / Real.Gamma b) * t ^ (b - a) < 1 := by
    calc
      (Real.Gamma a / Real.Gamma b) * t ^ (b - a) <
          (Real.Gamma a / Real.Gamma b) * crossing a b ^ (b - a) :=
        mul_lt_mul_of_pos_left hp hratio
      _ = 1 := crossing_factor_one ha hab
  rw [density_factor ha hb ht]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hf (density_pos ha ht)

private theorem density_lt_after_crossing {a b t : ℝ}
    (ha : 0 < a) (hab : a < b) (htc : crossing a b < t) :
    density a t < density b t := by
  have hb : 0 < b := lt_trans ha hab
  have ht : 0 < t := lt_trans (crossing_pos a b) htc
  have hratio : 0 < Real.Gamma a / Real.Gamma b :=
    div_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb)
  have hp := Real.rpow_lt_rpow (crossing_pos a b).le htc (sub_pos.mpr hab)
  have hf : 1 < (Real.Gamma a / Real.Gamma b) * t ^ (b - a) := by
    calc
      1 = (Real.Gamma a / Real.Gamma b) * crossing a b ^ (b - a) :=
        (crossing_factor_one ha hab).symm
      _ < (Real.Gamma a / Real.Gamma b) * t ^ (b - a) :=
        mul_lt_mul_of_pos_left hp hratio
  rw [density_factor ha hb ht]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hf (density_pos ha ht)

private def centered (a b t : ℝ) : ℝ :=
  (chi t - chi (crossing a b)) * (density b t - density a t)

private theorem centered_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (centered a b) (Ioi (0 : ℝ)) := by
  have hi := (chi_density_integrable hb).sub (chi_density_integrable ha)
  have hj := ((density_integrable hb).sub (density_integrable ha)).const_mul
    (chi (crossing a b))
  refine (hi.sub hj).congr_fun ?_ measurableSet_Ioi
  intro t ht
  change chi t * density b t - chi t * density a t -
      chi (crossing a b) * (density b t - density a t) = centered a b t
  unfold centered
  ring

private theorem integral_centered_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), centered a b t) =
      (∫ t in Ioi (0 : ℝ), chi t * density b t) -
        (∫ t in Ioi (0 : ℝ), chi t * density a t) := by
  have hiA := chi_density_integrable ha
  have hiB := chi_density_integrable hb
  have hdA := density_integrable ha
  have hdB := density_integrable hb
  have hiBA : IntegrableOn (fun t : ℝ =>
      chi t * density b t - chi t * density a t) (Ioi (0 : ℝ)) := hiB.sub hiA
  have hc : IntegrableOn (fun t : ℝ =>
      chi (crossing a b) * (density b t - density a t)) (Ioi (0 : ℝ)) :=
    (hdB.sub hdA).const_mul (chi (crossing a b))
  calc
    (∫ t in Ioi (0 : ℝ), centered a b t) =
        ∫ t in Ioi (0 : ℝ),
          chi t * density b t - chi t * density a t -
            chi (crossing a b) * (density b t - density a t) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      unfold centered
      ring
    _ = ((∫ t in Ioi (0 : ℝ), chi t * density b t) -
          (∫ t in Ioi (0 : ℝ), chi t * density a t)) -
        chi (crossing a b) *
          ((∫ t in Ioi (0 : ℝ), density b t) -
            (∫ t in Ioi (0 : ℝ), density a t)) := by
      rw [integral_sub hiBA hc, integral_sub hiB hiA,
        integral_const_mul, integral_sub hdB hdA]
    _ = (∫ t in Ioi (0 : ℝ), chi t * density b t) -
        (∫ t in Ioi (0 : ℝ), chi t * density a t) := by
      rw [density_mass hb, density_mass ha]
      ring

private theorem centered_pos_before_crossing {a b t : ℝ}
    (ha : 0 < a) (hab : a < b) (ht : 0 < t) (htc : t < crossing a b) :
    0 < centered a b t := by
  have hchi : chi t < chi (crossing a b) :=
    chi_strictMonoOn ht (crossing_pos a b) htc
  have hd := density_lt_before_crossing ha hab ht htc
  unfold centered
  exact mul_pos_of_neg_of_neg (sub_neg.mpr hchi) (sub_neg.mpr hd)

private theorem centered_nonneg {a b t : ℝ}
    (ha : 0 < a) (hab : a < b) (ht : 0 < t) : 0 ≤ centered a b t := by
  rcases lt_trichotomy t (crossing a b) with hlt | heq | hgt
  · exact (centered_pos_before_crossing ha hab ht hlt).le
  · rw [heq]
    simp only [centered, sub_self, zero_mul, le_refl]
  · have hchi : chi (crossing a b) < chi t :=
      chi_strictMonoOn (crossing_pos a b) ht hgt
    have hd := density_lt_after_crossing ha hab hgt
    unfold centered
    exact mul_nonneg (sub_pos.mpr hchi).le (sub_pos.mpr hd).le

private theorem chi_expectation_strict {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ t in Ioi (0 : ℝ), chi t * density a t) <
      (∫ t in Ioi (0 : ℝ), chi t * density b t) := by
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < crossing a b := crossing_pos a b
  have hi := centered_integrable ha hb
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] centered a b := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => centered_nonneg ha hab (mem_Ioi.mp ht))
  have hs : Ioo (0 : ℝ) (crossing a b) ⊆
      Function.support (centered a b) ∩ Ioi (0 : ℝ) := by
    intro t ht
    exact ⟨(centered_pos_before_crossing ha hab ht.1 ht.2).ne', ht.1⟩
  have hv : 0 < volume (Ioo (0 : ℝ) (crossing a b)) := by
    rw [Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr hc
  have hp : 0 < ∫ t in Ioi (0 : ℝ), centered a b t :=
    (setIntegral_pos_iff_support_of_nonneg_ae hn hi).2
      (lt_of_lt_of_le hv (measure_mono hs))
  rw [integral_centered_eq ha hb] at hp
  linarith

private theorem expectation_eq_half_add_chi {u : ℝ} (hu : 0 < u) :
    expectation u = u / 2 +
      ∫ t in Ioi (0 : ℝ), chi t * density u t := by
  have hm := (density_moment_integrable hu).div_const (2 : ℝ)
  have hc := chi_density_integrable hu
  calc
    expectation u = ∫ t in Ioi (0 : ℝ),
        (t * density u t) / 2 + chi t * density u t := by
      unfold expectation
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      unfold chi
      ring
    _ = (∫ t in Ioi (0 : ℝ), t * density u t) / 2 +
        ∫ t in Ioi (0 : ℝ), chi t * density u t := by
      rw [integral_add hm hc, integral_div]
    _ = u / 2 + ∫ t in Ioi (0 : ℝ), chi t * density u t := by
      rw [density_firstMoment hu]

private theorem gamma_expectation_strict_slope {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b - a) / 2 < expectation b - expectation a := by
  have hb : 0 < b := lt_trans ha hab
  have hchi := chi_expectation_strict ha hab
  rw [expectation_eq_half_add_chi hb, expectation_eq_half_add_chi ha]
  linarith

end GammaComparison

/-- Real normalized zeta in the positive macro coordinate. -/
def normalizedZeta (u : ℝ) : ℝ :=
  u * (riemannZeta ((1 + u : ℝ) : ℂ)).re

/-- The literal macro profile at the Euler amplitude. -/
def macroProfile (u : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant / normalizedZeta u

private theorem normalizedZeta_pos {u : ℝ} (hu : 0 < u) :
    0 < normalizedZeta u := by
  exact mul_pos hu (riemannZeta_re_pos_of_one_lt (by linarith))

private theorem normalizedZeta_strong_secant {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    (b - a) / 2 < normalizedZeta b - normalizedZeta a := by
  have hb : 0 < b := lt_trans ha hab
  have hqa : normalizedZeta a = GammaComparison.expectation a := by
    simpa only [normalizedZeta, GammaComparison.expectation,
      GammaComparison.psi, GammaComparison.density] using
      (Bose.actual_prefix_q_integral_binding ha).2
  have hqb : normalizedZeta b = GammaComparison.expectation b := by
    simpa only [normalizedZeta, GammaComparison.expectation,
      GammaComparison.psi, GammaComparison.density] using
      (Bose.actual_prefix_q_integral_binding hb).2
  rw [hqa, hqb]
  exact GammaComparison.gamma_expectation_strict_slope ha hab

/-- A strict quantitative decrease of the actual limiting prime-prefix ratio. -/
theorem result {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Real.exp Real.eulerMascheroniConstant * (b - a) /
        (2 * normalizedZeta a * normalizedZeta b) <
      macroProfile a - macroProfile b := by
  have hb : 0 < b := lt_trans ha hab
  have hqa := normalizedZeta_pos ha
  have hqb := normalizedZeta_pos hb
  have hc := Real.exp_pos Real.eulerMascheroniConstant
  have hs := normalizedZeta_strong_secant ha hab
  have hden := mul_pos hqa hqb
  have hscaled := (div_lt_div_iff_of_pos_right hden).2 (mul_lt_mul_of_pos_left hs hc)
  have hid : macroProfile a - macroProfile b =
      Real.exp Real.eulerMascheroniConstant *
        (normalizedZeta b - normalizedZeta a) /
          (normalizedZeta a * normalizedZeta b) := by
    unfold macroProfile
    field_simp [hqa.ne', hqb.ne']
    <;> ring
  rw [hid]
  simpa only [mul_div_assoc, div_div, mul_assoc] using hscaled

end D5.S3.Arith.Robin.PrimePrefixMacroProfile
end
