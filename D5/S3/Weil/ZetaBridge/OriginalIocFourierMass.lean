/- GID: D5/S3/Weil/ZetaBridge/OriginalIocFourierMass
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalIocFourierMass
   mirror-E: none(waiver:infinite-dimensional-analytic-identity)
   anchors: []
   utility: none
   digest: Preserve the original signed complex interval basis, Parseval mass and resonance-safe transform. -/

/-
  Original-Ioc Fourier dictionary, with the original dx normalization.

  This file keeps the original interval and the signed complex basis literal.
  The Parseval layer is discharged directly by Mathlib's public AddCircle
  owners.  No periodic endpoint condition is introduced: the circle lift is
  the literal `liftIoc` lift of the Ioc representative.
-/

import D5.S3.Weil.ZetaCore.PaperFT
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators ComplexConjugate

open Complex MeasureTheory Set Zeta23

noncomputable section

namespace D5.S3.Weil.ZetaBridge.OriginalIocFourier

/-! The original interval and its literal zero extension. -/

def interval (L : ℝ) : Set ℝ := Ioc (-L / 2) (L / 2)

def iocZeroExtend (L : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (interval L).indicator f

theorem interval_left_lt_right {L : ℝ} (hL : 0 < L) :
    -L / 2 < L / 2 := by
  linarith

theorem iocZeroExtend_eq_on_mem {L : ℝ} {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∈ interval L) : iocZeroExtend L f x = f x := by
  simp [iocZeroExtend, hx]

/-! The phase-adjusted signed basis and the corresponding coefficient. -/

def phase (n : ℤ) : ℂ := (-1 : ℂ) ^ n

def frequency (L : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * (n : ℝ) / L

def signedBasis (L : ℝ) (n : ℤ) : ℝ → ℂ :=
  iocZeroExtend L (fun x ↦
    phase n * (Real.sqrt L : ℂ)⁻¹ *
      Complex.exp (Complex.I * (frequency L n : ℂ) * (x : ℂ)))

def signedCoeff (L : ℝ) (hL : 0 < L) (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  phase n * (Real.sqrt L : ℂ) *
    fourierCoeffOn (interval_left_lt_right hL) f n

theorem norm_phase (n : ℤ) : ‖phase n‖ = 1 := by
  simp [phase]

theorem signedCoeff_sq {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (n : ℤ) :
    ‖signedCoeff L hL f n‖ ^ 2 =
      L * ‖fourierCoeffOn (interval_left_lt_right hL) f n‖ ^ 2 := by
  simp only [signedCoeff, norm_mul, norm_phase, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg L), mul_pow,
    Real.sq_sqrt hL.le]

/-! Parseval with the original dx mass and all signed modes. -/

theorem tsum_signedCoeff_sq_eq_mass {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hL2 : MemLp f 2 (volume.restrict (interval L))) :
    ∑' n : ℤ, ‖signedCoeff L hL f n‖ ^ 2 =
      ∫ x in (-L / 2)..(L / 2), ‖f x‖ ^ 2 := by
  have hsum := tsum_sq_fourierCoeffOn
    (interval_left_lt_right hL) hL2
  have hterm : ∀ n : ℤ,
      ‖signedCoeff L hL f n‖ ^ 2 =
        L * ‖fourierCoeffOn (interval_left_lt_right hL) f n‖ ^ 2 :=
    fun n ↦ signedCoeff_sq hL f n
  simp_rw [hterm]
  rw [tsum_mul_left, hsum]
  simp only [smul_eq_mul]
  have hsub : L / 2 - -L / 2 = L := by ring
  rw [hsub]
  field_simp [ne_of_gt hL]

/-! The centered exponential integral in a resonance-safe form.

  The branch at `r = 0` is part of the definition.  Away from the branch the
  expression is the usual rational sine form, while the first equality is the
  all-frequency statement used by the basis calculation.
-/

def centeredExpIntegral (L r : ℝ) : ℂ :=
  if r = 0 then (L : ℂ) else
    (Complex.exp (Complex.I * (r * L / 2 : ℝ)) -
      Complex.exp (-Complex.I * (r * L / 2 : ℝ))) /
      (Complex.I * (r : ℂ))

theorem integral_centered_exp {L r : ℝ} (hL : 0 < L) :
    (∫ x in (-L / 2)..(L / 2),
      Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))) =
        centeredExpIntegral L r := by
  by_cases hr : r = 0
  · subst r
    simp [centeredExpIntegral] <;> push_cast <;> ring
  · have hc : Complex.I * (r : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hr)
    have hb : Complex.I * (r : ℂ) * ((L / 2 : ℝ) : ℂ) =
        Complex.I * ((r * L / 2 : ℝ) : ℂ) := by push_cast; ring
    have ha : Complex.I * (r : ℂ) * ((-L / 2 : ℝ) : ℂ) =
        -Complex.I * ((r * L / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [integral_exp_mul_complex hc, hb, ha]
    simp only [centeredExpIntegral, if_neg hr]

theorem centeredExpIntegral_sinc {L r : ℝ} (hL : 0 < L) :
    (∫ x in (-L / 2)..(L / 2),
      Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))) =
        (L : ℂ) * (Real.sinc (r * L / 2) : ℂ) := by
  by_cases hr : r = 0
  · subst r
    simp [Real.sinc_zero] <;> push_cast <;> ring
  have h := intervalIntegral.integral_comp_mul_right
    (fun x : ℝ ↦ Complex.exp ((x : ℂ) * Complex.I))
    (a := -L / 2) (b := L / 2) hr
  have ha : -L / 2 * r = -(r * L / 2) := by ring
  have hb : L / 2 * r = r * L / 2 := by ring
  rw [ha, hb, integral_exp_mul_I_eq_sinc] at h
  have heq : (fun x : ℝ ↦ Complex.exp (((x * r : ℝ) : ℂ) * Complex.I)) =
      (fun x : ℝ ↦ Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))) := by
    funext x
    congr 1
    push_cast
    ring
  rw [heq] at h
  rw [h]
  simp only [real_smul, Complex.ofReal_inv]
  push_cast
  field_simp [hr]
  <;> ring

/-! Exact one-basis transform through the centered integral and the
    resonance-safe sinc expression. -/

def basisPaperFT (L : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  paperFT (signedBasis L n) t

theorem basisPaperFT_eq_centered {L : ℝ} (hL : 0 < L) (n : ℤ) (t : ℝ) :
    basisPaperFT L n t =
      phase n * (Real.sqrt L : ℂ)⁻¹ *
        (∫ x in (-L / 2)..(L / 2),
          Complex.exp (Complex.I * ((t + frequency L n : ℝ) : ℂ) * (x : ℂ))) := by
  unfold basisPaperFT signedBasis iocZeroExtend interval
  rw [Zeta23.paperFT_def]
  have hprod : ∀ x : ℝ,
      (Ioc (-L / 2) (L / 2)).indicator
          (fun y ↦ phase n * (Real.sqrt L : ℂ)⁻¹ *
            Complex.exp (Complex.I * (frequency L n : ℂ) * (y : ℂ))) x *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
        (Ioc (-L / 2) (L / 2)).indicator
          (fun y ↦ phase n * (Real.sqrt L : ℂ)⁻¹ *
            Complex.exp (Complex.I * (frequency L n : ℂ) * (y : ℂ)) *
              Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) x := by
    intro x
    by_cases hx : x ∈ Ioc (-L / 2) (L / 2)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  simp_rw [hprod]
  rw [integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : -L / 2 ≤ L / 2)]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem basisPaperFT_eq_sinc {L : ℝ} (hL : 0 < L) (n : ℤ) (t : ℝ) :
    basisPaperFT L n t =
      phase n * (Real.sqrt L : ℂ)⁻¹ *
        ((L : ℂ) * Real.sinc
          ((t + frequency L n) * L / 2)) := by
  rw [basisPaperFT_eq_centered hL]
  rw [centeredExpIntegral_sinc hL]

end D5.S3.Weil.ZetaBridge.OriginalIocFourier
