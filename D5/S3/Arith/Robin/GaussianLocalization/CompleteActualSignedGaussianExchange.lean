/- GID: D5/S3/Arith/Robin/GaussianLocalization/CompleteActualSignedGaussianExchange
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/GaussianLocalization/CompleteActualSignedGaussianExchange
   mirror-E: none(waiver:analytic-exchange-without-numeric-projection)
   anchors: []
   utility: none
   digest: Positive signed Gaussian W/K/v transforms and absolutely justified exchanges over every actual zeta-zero occurrence. -/

/- Source-only reconciliation of PR20756 against the byte-bound current suppliers.
   No compilation, axiom report or RH acceptance is claimed. The only scalar
   Gaussian owner is Fourier.Asymptotics.GaussianComplexMoments; no retired
   LowH, weighted, periodic or cubic branch is imported. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace
import D5.S3.Fourier.Asymptotics.GaussianComplexMoments
import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange

/-! The single actual H below is shared by every W/K/v formula. The
occurrence equivalence, conjugation permutation, strip, mass and height
certificates are proved or imported from the pinned actual suppliers. -/

open D5.S3.Fourier.Asymptotics.GaussianComplexMoments

def H (y : ℝ) : ℂ :=
  ∑' k : ℕ, (1 / (actualZero k * (1 - actualZero k))) *
    Complex.exp ((y : ℂ) * actualZero k)

/-- Original mean-16m, variance-2m density, retained literally. -/
def gaussianDensity (m y : ℝ) : ℝ :=
  Real.exp (-(y - 16 * m) ^ 2 / (4 * m)) / Real.sqrt (4 * Real.pi * m)

private theorem gaussianDensity_eq_scalar (m y : ℝ) :
    gaussianDensity m y =
      D5.S3.Fourier.Asymptotics.GaussianComplexMoments.gaussianDensity
        (16 * m) (2 * m) y := by
  dsimp only [gaussianDensity,
    D5.S3.Fourier.Asymptotics.GaussianComplexMoments.gaussianDensity]
  rw [show 2 * (2 * m) = 4 * m by ring,
    show 2 * Real.pi * (2 * m) = 4 * Real.pi * m by ring]

def gaussianU (m y : ℝ) : ℝ := (y - 16 * m) / (2 * m)

def gaussianP (m γ y : ℝ) : ℂ :=
  ((gaussianU m y : ℂ) + Complex.I * γ) *
      ((gaussianU m y : ℂ) + Complex.I * γ - 1) -
    1 / (2 * (m : ℂ))

def gaussianW (m γ y : ℝ) : ℂ :=
  -Complex.exp ((-Complex.I * γ) * (y : ℂ)) * gaussianP m γ y *
    (gaussianDensity m y : ℂ)

def gaussianK (m γ y : ℝ) : ℝ := (gaussianW m γ y).re

def gaussianV (m γ y : ℝ) : ℝ :=
  2 * (gaussianU m y ^ 2 + γ ^ 2 + 1) * gaussianDensity m y

private def quadraticAt (m γ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  -gaussianP m γ y * (gaussianDensity m y : ℂ) *
    Complex.exp (z * (y : ℂ))

private def envelopeAt (m γ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  (2 : ℂ) * ((gaussianU m y ^ 2 + γ ^ 2 + 1 : ℝ) : ℂ) *
    (gaussianDensity m y : ℂ) * Complex.exp (z * (y : ℂ))

private theorem quadratic_expansion (m γ : ℝ) (hm : 0 < m) (z : ℂ) (y : ℝ) :
    quadraticAt m γ z y =
      -(4 * (m : ℂ) ^ 2)⁻¹ * densityMonomial (16 * m) (2 * m) 2 z y +
      -(-2 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹ +
          (2 * Complex.I * (γ : ℂ) - 1) * (2 * (m : ℂ))⁻¹) *
        densityMonomial (16 * m) (2 * m) 1 z y +
      -(((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ -
          (2 * Complex.I * (γ : ℂ) - 1) * ((16 * m : ℝ) : ℂ) *
            (2 * (m : ℂ))⁻¹ - (γ : ℂ) ^ 2 - Complex.I * (γ : ℂ) -
          (2 * (m : ℂ))⁻¹) * densityMonomial (16 * m) (2 * m) 0 z y := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  dsimp [quadraticAt, gaussianP, gaussianU, densityMonomial]
  rw [gaussianDensity_eq_scalar]
  push_cast
  field_simp [hmC] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem envelope_expansion (m γ : ℝ) (hm : 0 < m) (z : ℂ) (y : ℝ) :
    envelopeAt m γ z y =
      (2 * (4 * (m : ℂ) ^ 2)⁻¹) * densityMonomial (16 * m) (2 * m) 2 z y +
      (-4 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹) *
        densityMonomial (16 * m) (2 * m) 1 z y +
      (2 * (((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ +
          (γ : ℂ) ^ 2 + 1)) * densityMonomial (16 * m) (2 * m) 0 z y := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  dsimp [envelopeAt, gaussianU, densityMonomial]
  rw [gaussianDensity_eq_scalar]
  push_cast
  field_simp [hmC] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem quadraticAt_integrable (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    Integrable (quadraticAt m γ z) := by
  have h2 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 2 z).const_mul
    (-(4 * (m : ℂ) ^ 2)⁻¹)
  have h1 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 1 z).const_mul
    (-(-2 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹ +
      (2 * Complex.I * (γ : ℂ) - 1) * (2 * (m : ℂ))⁻¹))
  have h0 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 0 z).const_mul
    (-(((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ -
      (2 * Complex.I * (γ : ℂ) - 1) * ((16 * m : ℝ) : ℂ) *
        (2 * (m : ℂ))⁻¹ - (γ : ℂ) ^ 2 - Complex.I * (γ : ℂ) -
      (2 * (m : ℂ))⁻¹))
  refine ((h2.add h1).add h0).congr (ae_of_all volume fun y => ?_)
  exact (quadratic_expansion m γ hm z y).symm

private theorem envelopeAt_integrable (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    Integrable (envelopeAt m γ z) := by
  have h2 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 2 z).const_mul
    (2 * (4 * (m : ℂ) ^ 2)⁻¹)
  have h1 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 1 z).const_mul
    (-4 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹)
  have h0 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 0 z).const_mul
    (2 * (((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ +
      (γ : ℂ) ^ 2 + 1))
  refine ((h2.add h1).add h0).congr (ae_of_all volume fun y => ?_)
  exact (envelope_expansion m γ hm z y).symm

private theorem quadraticAt_moment (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ, quadraticAt m γ z y) =
      -((z + Complex.I * (γ : ℂ)) ^ 2 -
        (z + Complex.I * (γ : ℂ))) * gaussianMGF (16 * m) (2 * m) z := by
  have h2 := density_moment_two (16 * m) (2 * m) (mul_pos (by norm_num) hm) z
  have h1 := density_moment_one (16 * m) (2 * m) (mul_pos (by norm_num) hm) z
  have h0 := density_moment_zero (16 * m) (2 * m) (mul_pos (by norm_num) hm) z
  have hi2 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 2 z).const_mul
    (-(4 * (m : ℂ) ^ 2)⁻¹)
  have hi1 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 1 z).const_mul
    (-(-2 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹ +
      (2 * Complex.I * (γ : ℂ) - 1) * (2 * (m : ℂ))⁻¹))
  have hi0 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 0 z).const_mul
    (-(((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ -
      (2 * Complex.I * (γ : ℂ) - 1) * ((16 * m : ℝ) : ℂ) *
        (2 * (m : ℂ))⁻¹ - (γ : ℂ) ^ 2 - Complex.I * (γ : ℂ) -
      (2 * (m : ℂ))⁻¹))
  calc
    (∫ y : ℝ, quadraticAt m γ z y) =
        (-(4 * (m : ℂ) ^ 2)⁻¹) * (∫ y : ℝ, densityMonomial (16 * m) (2 * m) 2 z y) +
        (-(-2 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹ +
          (2 * Complex.I * (γ : ℂ) - 1) * (2 * (m : ℂ))⁻¹)) *
          (∫ y : ℝ, densityMonomial (16 * m) (2 * m) 1 z y) +
        (-(((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ -
          (2 * Complex.I * (γ : ℂ) - 1) * ((16 * m : ℝ) : ℂ) *
            (2 * (m : ℂ))⁻¹ - (γ : ℂ) ^ 2 - Complex.I * (γ : ℂ) -
          (2 * (m : ℂ))⁻¹)) * (∫ y : ℝ, densityMonomial (16 * m) (2 * m) 0 z y) := by
      rw [integral_congr_ae (ae_of_all volume fun y =>
        quadratic_expansion m γ hm z y)]
      have h21 := integral_add hi2 hi1
      have h210 := integral_add (hi2.add hi1) hi0
      simp only [Pi.add_apply] at h21 h210
      rw [h210, h21]
      simp only [integral_const_mul]
    _ = _ := by
      rw [h2, h1, h0]
      dsimp [tiltedMean, gaussianMGF, gaussianExponent]
      push_cast
      field_simp [(show (m : ℂ) ≠ 0 by exact_mod_cast hm.ne')]
        <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem envelopeAt_moment (m γ : ℝ) (hm : 0 < m) (z : ℂ) :
    (∫ y : ℝ, envelopeAt m γ z y) =
      2 * (z ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) *
        gaussianMGF (16 * m) (2 * m) z := by
  have h2 := density_moment_two (16 * m) (2 * m) (mul_pos (by norm_num) hm) z
  have h1 := density_moment_one (16 * m) (2 * m) (mul_pos (by norm_num) hm) z
  have h0 := density_moment_zero (16 * m) (2 * m) (mul_pos (by norm_num) hm) z
  have hi2 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 2 z).const_mul
    (2 * (4 * (m : ℂ) ^ 2)⁻¹)
  have hi1 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 1 z).const_mul
    (-4 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹)
  have hi0 := (density_monomial_integrable (16 * m) (2 * m) (mul_pos (by norm_num) hm) 0 z).const_mul
    (2 * (((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ +
      (γ : ℂ) ^ 2 + 1))
  calc
    (∫ y : ℝ, envelopeAt m γ z y) =
        (2 * (4 * (m : ℂ) ^ 2)⁻¹) * (∫ y : ℝ, densityMonomial (16 * m) (2 * m) 2 z y) +
        (-4 * ((16 * m : ℝ) : ℂ) * (4 * (m : ℂ) ^ 2)⁻¹) *
          (∫ y : ℝ, densityMonomial (16 * m) (2 * m) 1 z y) +
        (2 * (((16 * m : ℝ) : ℂ) ^ 2 * (4 * (m : ℂ) ^ 2)⁻¹ +
          (γ : ℂ) ^ 2 + 1)) * (∫ y : ℝ, densityMonomial (16 * m) (2 * m) 0 z y) := by
      rw [integral_congr_ae (ae_of_all volume fun y =>
        envelope_expansion m γ hm z y)]
      have h21 := integral_add hi2 hi1
      have h210 := integral_add (hi2.add hi1) hi0
      simp only [Pi.add_apply] at h21 h210
      rw [h210, h21]
      simp only [integral_const_mul]
    _ = _ := by
      rw [h2, h1, h0]
      dsimp [tiltedMean, gaussianMGF, gaussianExponent]
      push_cast
      field_simp [(show (m : ℂ) ≠ 0 by exact_mod_cast hm.ne')]
        <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/- Multiplication is rearranged only after the exponential addition identity is
   applied to adjacent factors.  All parameters here remain complex. -/
private theorem quadraticAt_shift (m γ : ℝ) (z t : ℂ) (y : ℝ) :
    Complex.exp (t * (y : ℂ)) * quadraticAt m γ z y =
      quadraticAt m γ (t + z) y := by
  dsimp only [quadraticAt]
  rw [add_mul, Complex.exp_add]
  ring

private theorem envelopeAt_shift (m γ : ℝ) (z t : ℂ) (y : ℝ) :
    Complex.exp (t * (y : ℂ)) * envelopeAt m γ z y =
      envelopeAt m γ (t + z) y := by
  dsimp only [envelopeAt]
  rw [add_mul, Complex.exp_add]
  ring

/-- A paid domination argument for the full positive and negative real axes. -/
private theorem weighted_norm_integrable (q : ℝ → ℂ)
    (hq : Integrable q) (hshift : Integrable (fun y : ℝ => Real.exp y • q y))
    (hc : Continuous q) :
    Integrable (fun y : ℝ => Real.exp (max y 0) * ‖q y‖) := by
  have hmaj : Integrable (fun y : ℝ => ‖q y‖ + ‖Real.exp y • q y‖) :=
    hq.norm.add hshift.norm
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => Real.exp (max y 0) * ‖q y‖) volume := by
    have hcont : Continuous (fun y : ℝ => Real.exp (max y 0) * ‖q y‖) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  refine hmaj.mono' hmeas (ae_of_all volume fun y => ?_)
  have hmax : Real.exp (max y 0) ≤ 1 + Real.exp y := by
    by_cases hy : 0 ≤ y
    · rw [max_eq_left hy]
      linarith [Real.exp_nonneg y]
    · rw [max_eq_right (le_of_not_ge hy), Real.exp_zero]
      linarith [Real.exp_nonneg y]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))]
  calc
    Real.exp (max y 0) * ‖q y‖ ≤ (1 + Real.exp y) * ‖q y‖ :=
      mul_le_mul_of_nonneg_right hmax (norm_nonneg _)
    _ = ‖q y‖ + ‖Real.exp y • q y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      ring

private theorem weighted_quadratic_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => Real.exp (max y 0) *
      ‖quadraticAt m γ (-Complex.I * γ) y‖) := by
  have hshift : Integrable (fun y : ℝ =>
      Real.exp y • quadraticAt m γ (-Complex.I * γ) y) := by
    have hq := quadraticAt_integrable m γ hm (1 + (-Complex.I * γ))
    refine hq.congr (ae_of_all volume fun y => ?_)
    change quadraticAt m γ (1 + (-Complex.I * γ)) y =
      (Real.exp y : ℂ) * quadraticAt m γ (-Complex.I * γ) y
    rw [← quadraticAt_shift m γ (-Complex.I * γ) 1 y]
    simp only [one_mul, Complex.ofReal_exp]
  have hc : Continuous (quadraticAt m γ (-Complex.I * γ)) := by
    unfold quadraticAt gaussianP gaussianU gaussianDensity
    fun_prop
  exact weighted_norm_integrable _
    (quadraticAt_integrable m γ hm (-Complex.I * γ)) hshift hc

private theorem weighted_envelope_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => Real.exp (max y 0) * ‖envelopeAt m γ 0 y‖) := by
  have hshift : Integrable (fun y : ℝ => Real.exp y • envelopeAt m γ 0 y) := by
    have hq := envelopeAt_integrable m γ hm 1
    refine hq.congr (ae_of_all volume fun y => ?_)
    change envelopeAt m γ 1 y =
      (Real.exp y : ℂ) * envelopeAt m γ 0 y
    simpa only [one_mul, add_zero, Complex.ofReal_exp] using
      (envelopeAt_shift m γ 0 1 y).symm
  have hc : Continuous (envelopeAt m γ 0) := by
    unfold envelopeAt gaussianU gaussianDensity
    fun_prop
  exact weighted_norm_integrable _ (envelopeAt_integrable m γ hm 0) hshift hc

private theorem gaussianW_eq_quadratic (m γ : ℝ) (y : ℝ) :
    gaussianW m γ y = quadraticAt m γ (-Complex.I * γ) y := by
  dsimp only [gaussianW, quadraticAt]
  ring

private theorem gaussianV_eq_envelope (m γ : ℝ) (y : ℝ) :
    (gaussianV m γ y : ℂ) = envelopeAt m γ 0 y := by
  simp only [gaussianV, envelopeAt, zero_mul, Complex.exp_zero, mul_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- Genuine weighted integrability of W, for every m>0 and every real γ. -/
theorem gaussianW_weighted_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => Real.exp (max y 0) * ‖gaussianW m γ y‖) := by
  simpa only [gaussianW_eq_quadratic] using weighted_quadratic_integrable m γ hm

/-- Genuine weighted integrability of the exact real envelope v. -/
theorem gaussianV_weighted_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => Real.exp (max y 0) * ‖(gaussianV m γ y : ℂ)‖) := by
  simpa only [gaussianV_eq_envelope] using weighted_envelope_integrable m γ hm

private theorem gaussianW_tilt_eq (m γ : ℝ) (ρ : ℂ) (y : ℝ) :
    Complex.exp (ρ * (y : ℂ)) * gaussianW m γ y =
      quadraticAt m γ (ρ - Complex.I * γ) y := by
  rw [gaussianW_eq_quadratic, quadraticAt_shift]
  congr 1
  ring

private theorem gaussianV_tilt_eq (m γ : ℝ) (ρ : ℂ) (y : ℝ) :
    Complex.exp (ρ * (y : ℂ)) * (gaussianV m γ y : ℂ) =
      envelopeAt m γ ρ y := by
  rw [gaussianV_eq_envelope, envelopeAt_shift, add_zero]

/-- Exact signed complex W transform; its minus sign belongs here. -/
theorem gaussianW_transform (m γ : ℝ) (hm : 0 < m) (ρ : ℂ) :
    (∫ y : ℝ, Complex.exp (ρ * (y : ℂ)) * gaussianW m γ y) =
      -ρ * (ρ - 1) * Complex.exp
        ((m : ℂ) * (ρ - Complex.I * γ) ^ 2 +
          (16 * (m : ℂ)) * (ρ - Complex.I * γ)) := by
  simp_rw [gaussianW_tilt_eq]
  rw [quadraticAt_moment m γ hm (ρ - Complex.I * γ)]
  have hE : gaussianExponent (16 * m) (2 * m) (ρ - Complex.I * γ) =
      (m : ℂ) * (ρ - Complex.I * γ) ^ 2 +
        (16 * (m : ℂ)) * (ρ - Complex.I * γ) := by
    dsimp only [gaussianExponent]
    push_cast
    ring
  simp only [gaussianMGF, hE]
  have harg : ρ - Complex.I * (γ : ℂ) + Complex.I * (γ : ℂ) = ρ := by ring
  rw [harg]
  ring

/-- Exact complex transform of the full envelope, with the variance correction. -/
theorem gaussianV_transform (m γ : ℝ) (hm : 0 < m) (ρ : ℂ) :
    (∫ y : ℝ, Complex.exp (ρ * (y : ℂ)) * (gaussianV m γ y : ℂ)) =
      2 * (ρ ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) *
        Complex.exp ((m : ℂ) * ρ ^ 2 + (16 * (m : ℂ)) * ρ) := by
  simp_rw [gaussianV_tilt_eq]
  rw [envelopeAt_moment m γ hm ρ]
  have hE : gaussianExponent (16 * m) (2 * m) ρ =
      (m : ℂ) * ρ ^ 2 + (16 * (m : ℂ)) * ρ := by
    dsimp only [gaussianExponent]
    push_cast
    ring
  simpa only [gaussianMGF, hE]

private theorem gaussianP_norm_le (m γ y : ℝ) (hm : 1 ≤ m) :
    ‖gaussianP m γ y‖ ≤ 2 * (gaussianU m y ^ 2 + γ ^ 2 + 1) := by
  let u : ℝ := gaussianU m y
  let A : ℂ := (u : ℂ) + Complex.I * γ
  let B : ℂ := (u : ℂ) + Complex.I * γ - 1
  have hA : ‖A‖ ^ 2 = u ^ 2 + γ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [A, pow_two]
  have hB : ‖B‖ ^ 2 = (u - 1) ^ 2 + γ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [B, pow_two]
  have hAB : ‖A‖ * ‖B‖ ≤ (‖A‖ ^ 2 + ‖B‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
  rw [hA, hB] at hAB
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hhalf : 1 / (2 * m) ≤ (1 : ℝ) / 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m) (by norm_num)).2
    nlinarith
  have hden : ‖(1 / (2 * (m : ℂ)) : ℂ)‖ = 1 / (2 * m) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmpos]
  change ‖A * B - 1 / (2 * (m : ℂ))‖ ≤ 2 * (u ^ 2 + γ ^ 2 + 1)
  calc
    ‖A * B - 1 / (2 * (m : ℂ))‖ ≤ ‖A‖ * ‖B‖ + 1 / (2 * m) := by
      simpa only [norm_mul, hden] using norm_sub_le (A * B) (1 / (2 * (m : ℂ)))
    _ ≤ 2 * (u ^ 2 + γ ^ 2 + 1) := by
      nlinarith [sq_nonneg (u + (1 / 2 : ℝ)), sq_nonneg γ]

/-- Both pointwise inequalities, on the entire real axis, for every m≥1. -/
theorem gaussian_kernel_domination (m γ y : ℝ) (hm : 1 ≤ m) :
    ‖(gaussianK m γ y : ℂ)‖ ≤ gaussianV m γ y ∧
      0 ≤ gaussianK m γ y + gaussianV m γ y := by
  have hg : 0 ≤ gaussianDensity m y := by
    dsimp [gaussianDensity]
    positivity
  have hp := gaussianP_norm_le m γ y hm
  have hphase : ‖Complex.exp ((-Complex.I * γ) * (y : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hw : ‖gaussianW m γ y‖ ≤ gaussianV m γ y := by
    have heq : ‖gaussianW m γ y‖ = ‖gaussianP m γ y‖ * gaussianDensity m y := by
      dsimp only [gaussianW]
      rw [norm_mul, norm_mul, norm_neg, hphase]
      simp only [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
    rw [heq]
    exact mul_le_mul_of_nonneg_right hp hg
  have habs : |gaussianK m γ y| ≤ gaussianV m γ y :=
    (Complex.abs_re_le_norm (gaussianW m γ y)).trans hw
  constructor
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using habs
  · have hge := (abs_le.mp habs).1
    linarith

/-- True measurability of the actual infinite exponential sum. -/
theorem H_measurable : Measurable H := by
  unfold H
  apply Measurable.tsum
  intro k
  fun_prop

private theorem H_mul_weight_integrable (w : ℝ → ℂ)
    (hw : AEStronglyMeasurable w volume)
    (hwi : Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖)) :
    Integrable (fun y : ℝ => H y * w y) := by
  have hbase : Integrable (fun y : ℝ =>
      ((101 / 100 : ℝ) * firstLiMass) * (Real.exp (max y 0) * ‖w y‖)) :=
    hwi.const_mul ((101 / 100 : ℝ) * firstLiMass)
  have hmeas : AEStronglyMeasurable (fun y : ℝ => H y * w y) volume :=
    H_measurable.aestronglyMeasurable.mul hw
  refine hbase.mono' hmeas (ae_of_all volume fun y => ?_)
  obtain ⟨_, _, _, hp, _⟩ := D5.S3.Weil.Mertens.IntegratedExplicit.actual_complete_H_package
  have hbound : ‖H y‖ ≤
      ((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0) := by
    simpa only [H] using (hp y).2.2
  calc
    ‖H y * w y‖ = ‖H y‖ * ‖w y‖ := norm_mul _ _
    _ ≤ (((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0)) * ‖w y‖ :=
      mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = _ := by ring

/-- Actual complex product integrability, prior to any use of integral identities. -/
theorem H_weighted_product_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => H y * gaussianW m γ y) := by
  have hc : Continuous (gaussianW m γ) := by
    unfold gaussianW gaussianP gaussianU gaussianDensity
    fun_prop
  exact H_mul_weight_integrable _ hc.aestronglyMeasurable
    (gaussianW_weighted_integrable m γ hm)

theorem H_weighted_V_product_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => H y * (gaussianV m γ y : ℂ)) := by
  have hc : Continuous (fun y : ℝ => (gaussianV m γ y : ℂ)) := by
    unfold gaussianV gaussianU gaussianDensity
    fun_prop
  exact H_mul_weight_integrable _ hc.aestronglyMeasurable
    (gaussianV_weighted_integrable m γ hm)

private theorem H_im_zero (y : ℝ) : (H y).im = 0 := by
  obtain ⟨_, _, _, hp, _⟩ := D5.S3.Weil.Mertens.IntegratedExplicit.actual_complete_H_package
  exact (hp y).2.1

private theorem real_product_eq_re (m γ y : ℝ) :
    (H y).re * gaussianK m γ y = (H y * gaussianW m γ y).re := by
  rw [Complex.mul_re, H_im_zero, zero_mul, sub_zero]
  rfl

/-- The real K integral is a genuine Bochner integral of an integrable function. -/
theorem H_real_K_product_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => (H y).re * gaussianK m γ y) := by
  refine (H_weighted_product_integrable m γ hm).re.congr
    (ae_of_all volume fun y => ?_)
  exact (real_product_eq_re m γ y).symm

theorem H_real_V_product_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => (H y).re * gaussianV m γ y) := by
  have hv := (H_weighted_V_product_integrable m γ hm).re
  refine hv.congr (ae_of_all volume fun y => ?_)
  simp [Complex.mul_re]

private theorem signed_reciprocal_cancellation (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    (1 / (ρ * (1 - ρ))) * (-ρ * (ρ - 1)) = 1 := by
  field_simp [h0, sub_ne_zero.mpr h1.symm]
  <;> ring

/-- Actual occurrence exchange. The coefficient cancels BOTH minus signs. -/
theorem actual_signed_W_exchange (m γ : ℝ) (hm : 0 < m) :
    HasSum
      (fun k : ℕ =>
        Complex.exp ((m : ℂ) * (actualZero k - Complex.I * γ) ^ 2 +
          (16 * (m : ℂ)) * (actualZero k - Complex.I * γ)))
      (∫ y : ℝ, H y * gaussianW m γ y) := by
  have hcW : Continuous (gaussianW m γ) := by
    unfold gaussianW gaussianP gaussianU gaussianDensity
    fun_prop
  obtain ⟨_, _, _, _, hex⟩ :=
    D5.S3.Weil.Mertens.IntegratedExplicit.actual_complete_H_package
  have he : HasSum (fun k : ℕ =>
      (1 / (actualZero k * (1 - actualZero k))) *
        ∫ y : ℝ, Complex.exp ((y : ℂ) * actualZero k) * gaussianW m γ y)
      (∫ y : ℝ, H y * gaussianW m γ y) := by
    simpa only [H] using
      hex (gaussianW m γ) hcW.aestronglyMeasurable
        (gaussianW_weighted_integrable m γ hm)
  have hcongr : ∀ k : ℕ,
      (1 / (actualZero k * (1 - actualZero k))) *
          (∫ y : ℝ, Complex.exp ((y : ℂ) * actualZero k) * gaussianW m γ y) =
        Complex.exp ((m : ℂ) * (actualZero k - Complex.I * γ) ^ 2 +
          (16 * (m : ℂ)) * (actualZero k - Complex.I * γ)) := by
    intro k
    have ht : (fun y : ℝ => Complex.exp ((y : ℂ) * actualZero k) *
        gaussianW m γ y) =
        (fun y : ℝ => Complex.exp (actualZero k * (y : ℂ)) *
          gaussianW m γ y) := by
      funext y
      rw [mul_comm (y : ℂ) (actualZero k)]
    rw [ht, gaussianW_transform m γ hm (actualZero k)]
    have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
    have h0 : actualZero k ≠ 0 := by
      intro h
      have ht0 := hs.1
      change 0 < (actualZero k).re at ht0
      simpa only [h, Complex.zero_re, lt_self_iff_false] using ht0
    have h1 : actualZero k ≠ 1 := by
      intro h
      have ht1 := hs.2
      change (actualZero k).re < 1 at ht1
      simpa only [h, Complex.one_re, lt_self_iff_false] using ht1
    rw [← mul_assoc, signed_reciprocal_cancellation _ h0 h1, one_mul]
  exact he.congr_fun (fun k => (hcongr k).symm)

/-- Complete envelope exchange, retaining all complex reciprocal coefficients. -/
theorem actual_signed_V_exchange (m γ : ℝ) (hm : 0 < m) :
    HasSum
      (fun k : ℕ =>
        (1 / (actualZero k * (1 - actualZero k))) *
          (2 * (actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1 +
            1 / (2 * (m : ℂ))) *
            Complex.exp ((m : ℂ) * actualZero k ^ 2 +
              (16 * (m : ℂ)) * actualZero k)))
      (∫ y : ℝ, H y * (gaussianV m γ y : ℂ)) := by
  have hcV : Continuous (fun y : ℝ => (gaussianV m γ y : ℂ)) := by
    dsimp [gaussianV, gaussianU, gaussianDensity]
    fun_prop
  obtain ⟨_, _, _, _, hex⟩ :=
    D5.S3.Weil.Mertens.IntegratedExplicit.actual_complete_H_package
  have he : HasSum (fun k : ℕ =>
      (1 / (actualZero k * (1 - actualZero k))) *
        ∫ y : ℝ, Complex.exp ((y : ℂ) * actualZero k) * (gaussianV m γ y : ℂ))
      (∫ y : ℝ, H y * (gaussianV m γ y : ℂ)) := by
    simpa only [H] using
      hex (fun y : ℝ => (gaussianV m γ y : ℂ)) hcV.aestronglyMeasurable
        (gaussianV_weighted_integrable m γ hm)
  have hcongr : ∀ k : ℕ,
      (1 / (actualZero k * (1 - actualZero k))) *
          (∫ y : ℝ, Complex.exp ((y : ℂ) * actualZero k) *
            (gaussianV m γ y : ℂ)) =
        (1 / (actualZero k * (1 - actualZero k))) *
          (2 * (actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1 +
            1 / (2 * (m : ℂ))) *
            Complex.exp ((m : ℂ) * actualZero k ^ 2 +
              (16 * (m : ℂ)) * actualZero k)) := by
    intro k
    have ht : (fun y : ℝ => Complex.exp ((y : ℂ) * actualZero k) *
        (gaussianV m γ y : ℂ)) =
        (fun y : ℝ => Complex.exp (actualZero k * (y : ℂ)) *
          (gaussianV m γ y : ℂ)) := by
      funext y
      rw [mul_comm (y : ℂ) (actualZero k)]
    rw [ht, gaussianV_transform m γ hm (actualZero k)]
  exact he.congr_fun (fun k => (hcongr k).symm)

/-- Full positive shifted-exponential sum, with real-part passage AFTER integrability. -/
theorem actual_signed_K_exchange (m γ : ℝ) (hm : 0 < m) :
    ∫ y : ℝ, (H y).re * gaussianK m γ y =
      (∑' k : ℕ,
        Complex.exp ((m : ℂ) * (actualZero k - Complex.I * γ) ^ 2 +
          (16 * (m : ℂ)) * (actualZero k - Complex.I * γ))).re := by
  have hsum := actual_signed_W_exchange m γ hm
  have hI := H_weighted_product_integrable m γ hm
  calc
    ∫ y : ℝ, (H y).re * gaussianK m γ y =
        ∫ y : ℝ, (H y * gaussianW m γ y).re := by
      apply integral_congr_ae
      exact ae_of_all volume fun y => real_product_eq_re m γ y
    _ = (∫ y : ℝ, H y * gaussianW m γ y).re := integral_re hI
    _ = (∑' k : ℕ,
        Complex.exp ((m : ℂ) * (actualZero k - Complex.I * γ) ^ 2 +
          (16 * (m : ℂ)) * (actualZero k - Complex.I * γ))).re := by
      rw [hsum.tsum_eq]




end D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange

end
