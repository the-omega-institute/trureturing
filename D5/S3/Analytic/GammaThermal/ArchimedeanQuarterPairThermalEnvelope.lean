/- GID: D5/S3/Analytic/GammaThermal/ArchimedeanQuarterPairThermalEnvelope
   generality: I
   mirror-B: D5/B/S3/Analytic/GammaThermal/ArchimedeanQuarterPairThermalEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The quarter-shifted Gamma pair has an exact Fermi-like thermal envelope. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexConjugate

namespace D5.S3.Analytic.GammaThermal.ArchimedeanQuarterPairThermalEnvelope

/-- The Archimedean quarter-line Gamma channel `G_+`. -/
def archimedeanGammaPlus (t : ℝ) : ℂ :=
  Complex.Gamma ((1 : ℂ) / 4 + Complex.I * ((t : ℂ) / 2))

/-- The complementary three-quarter-line Gamma channel `G_-`. -/
def archimedeanGammaMinus (t : ℝ) : ℂ :=
  Complex.Gamma ((3 : ℂ) / 4 + Complex.I * ((t : ℂ) / 2))

private lemma gamma_half_line_normSq (t : ℝ) :
    Complex.normSq
        (Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (t : ℂ))) =
      Real.pi / Real.cosh (Real.pi * t) := by
  have hsin :
      Complex.sin
          ((Real.pi : ℂ) * ((1 : ℂ) / 2 + Complex.I * (t : ℂ))) =
        (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show
      (Real.pi : ℂ) * ((1 : ℂ) / 2 + Complex.I * (t : ℂ)) =
        (Real.pi / 2 : ℝ) + (Real.pi * t : ℝ) * Complex.I by
          push_cast
          ring]
    simp [Complex.sin_add_mul_I]
  rw [← Complex.ofReal_inj]
  calc
    (Complex.normSq
          (Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (t : ℂ))) : ℂ) =
        conj
            (Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (t : ℂ))) *
          Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (t : ℂ)) :=
      Complex.normSq_eq_conj_mul_self
    _ = Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (t : ℂ)) *
          Complex.Gamma
            (conj ((1 : ℂ) / 2 + Complex.I * (t : ℂ))) := by
      rw [Complex.Gamma_conj]
      ring
    _ = Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (t : ℂ)) *
          Complex.Gamma
            (1 - ((1 : ℂ) / 2 + Complex.I * (t : ℂ))) := by
      congr 2
      apply Complex.ext <;> norm_num
    _ = (Real.pi : ℂ) /
          Complex.sin
            ((Real.pi : ℂ) * ((1 : ℂ) / 2 + Complex.I * (t : ℂ))) :=
      Complex.Gamma_mul_Gamma_one_sub _
    _ = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
      rw [hsin]
      norm_cast

private lemma gamma_quarter_pair_product (t : ℝ) :
    archimedeanGammaPlus t * archimedeanGammaMinus t =
      Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (t : ℂ)) *
        (2 : ℂ) ^ ((1 : ℂ) / 2 - Complex.I * (t : ℂ)) *
        (Real.sqrt Real.pi : ℂ) := by
  unfold archimedeanGammaPlus archimedeanGammaMinus
  convert Complex.Gamma_mul_Gamma_add_half
    ((1 : ℂ) / 4 + Complex.I * ((t : ℂ) / 2)) using 1 <;> ring_nf

private lemma two_cpow_quarter_normSq (t : ℝ) :
    Complex.normSq
        ((2 : ℂ) ^ ((1 : ℂ) / 2 - Complex.I * (t : ℂ))) = 2 := by
  change Complex.normSq
      (((2 : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - Complex.I * (t : ℂ))) = 2
  rw [Complex.normSq_eq_norm_sq]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ))
    (by norm_num : (0 : ℝ) < 2)]
  rw [show
    (((1 : ℂ) / 2 - Complex.I * (t : ℂ))).re = (1 / 2 : ℝ) by simp]
  rw [← Real.sqrt_eq_rpow]
  norm_num

private lemma gamma_quarter_pair_norm_identity (t : ℝ) :
    ‖archimedeanGammaPlus t‖ ^ 2 * ‖archimedeanGammaMinus t‖ ^ 2 =
      2 * Real.pi ^ 2 / Real.cosh (Real.pi * t) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_mul, gamma_quarter_pair_product,
    Complex.normSq_mul, Complex.normSq_mul, gamma_half_line_normSq,
    two_cpow_quarter_normSq, Complex.normSq_ofReal,
    Real.mul_self_sqrt Real.pi_nonneg]
  ring

private lemma reciprocal_cosh_fermi_identity (t : ℝ) :
    1 / Real.cosh (Real.pi * t) =
      2 * Real.exp (-Real.pi * |t|) /
        (1 + Real.exp (-2 * Real.pi * |t|)) := by
  have hcosh :
      Real.cosh (Real.pi * t) = Real.cosh (Real.pi * |t|) := by
    rw [← Real.cosh_abs (Real.pi * t)]
    congr 1
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hexp : Real.exp (Real.pi * |t|) ≠ 0 :=
    (Real.exp_pos (Real.pi * |t|)).ne'
  have hnegTwo :
      Real.exp (-2 * Real.pi * |t|) =
        (Real.exp (Real.pi * |t|))⁻¹ *
          (Real.exp (Real.pi * |t|))⁻¹ := by
    rw [show
      -2 * Real.pi * |t| =
        -(Real.pi * |t|) + -(Real.pi * |t|) by ring,
      Real.exp_add, Real.exp_neg]
  rw [hcosh]
  rw [Real.cosh_eq, Real.exp_neg, hnegTwo]
  field_simp [Real.exp_neg, hexp]
  rw [← Real.exp_add]
  ring_nf
  simp

/-- The two quarter-shifted Archimedean Gamma channels have the exact squared-norm
thermal envelope, and the reciprocal hyperbolic cosine has its strict
Fermi-like exponential form. -/
theorem archimedean_quarter_pair_thermal_envelope (t : ℝ) :
    ‖archimedeanGammaPlus t‖ ^ 2 * ‖archimedeanGammaMinus t‖ ^ 2 =
        2 * Real.pi ^ 2 / Real.cosh (Real.pi * t) ∧
      1 / Real.cosh (Real.pi * t) =
        2 * Real.exp (-Real.pi * |t|) /
          (1 + Real.exp (-2 * Real.pi * |t|)) :=
  ⟨gamma_quarter_pair_norm_identity t, reciprocal_cosh_fermi_identity t⟩

-- Reverse probe for CAS assertion A1: the public theorem makes the quarter-pair
-- product strictly positive at the central parameter.
example :
    0 < ‖archimedeanGammaPlus 0‖ ^ 2 * ‖archimedeanGammaMinus 0‖ ^ 2 := by
  rw [(archimedean_quarter_pair_thermal_envelope 0).1]
  positivity

-- Reverse probe for CAS assertion A2: the public theorem transfers positivity
-- of reciprocal cosh to the complete Fermi-like exponential expression.
example (t : ℝ) :
    0 < 2 * Real.exp (-Real.pi * |t|) /
      (1 + Real.exp (-2 * Real.pi * |t|)) := by
  rw [← (archimedean_quarter_pair_thermal_envelope t).2]
  exact one_div_pos.mpr (Real.cosh_pos _)

end D5.S3.Analytic.GammaThermal.ArchimedeanQuarterPairThermalEnvelope
