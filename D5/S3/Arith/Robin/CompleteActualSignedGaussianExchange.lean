/- GID: D5/S3/Arith/Robin/CompleteActualSignedGaussianExchange
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/CompleteActualSignedGaussianExchange
   mirror-E: none(waiver:analytic-exchange-without-numeric-projection)
   anchors: []
   utility: none
   digest: Positive signed Gaussian W/K/v transforms and absolutely justified exchanges over every actual zeta-zero occurrence. -/

/- Source-only preparation against dev 65da818fcf9a0a4a9b3558bd2a6d3ead6760da57.
   No compilation, axiom report or RH acceptance is claimed. The only scalar
   Gaussian owner is Fourier.Asymptotics.GaussianComplexMoments; no retired
   LowH, weighted, periodic or cubic branch is imported. -/

import D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
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

private theorem actual_occurrence_mass_symmetry_growth_exchange :
    let a : ℕ → ℂ := fun k => 1 / (actualZero k * (1 - actualZero k))
    HasSum a (firstLiMass : ℂ) ∧
      ∃ c : Equiv.Perm ℕ,
        (∀ k : ℕ, actualZero (c k) = conj (actualZero k)) ∧
        (∀ y : ℝ,
          Summable (fun k : ℕ => a k * Complex.exp ((y : ℂ) * actualZero k)) ∧
          (∑' k : ℕ, a k * Complex.exp ((y : ℂ) * actualZero k)).im = 0 ∧
          ‖∑' k : ℕ, a k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
            ((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0)) ∧
        (∀ w : ℝ → ℂ, AEStronglyMeasurable w volume →
          Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖) →
          HasSum
            (fun k : ℕ => a k * ∫ y : ℝ,
              Complex.exp ((y : ℂ) * actualZero k) * w y)
            (∫ y : ℝ,
              (∑' k : ℕ, a k * Complex.exp ((y : ℂ) * actualZero k)) * w y)) := by
  classical
  dsimp only
  let a : ℕ → ℂ := fun k => 1 / (actualZero k * (1 - actualZero k))
  have hx1 : xiReading 1 ≠ 0 := by
    rw [xi_reading_endpoint_values.2]
    norm_num
  have hres := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have href : logDeriv xiReading 0 = -logDeriv xiReading 1 := by
    simpa only [sub_self] using xi_logDeriv_reflection (1 : ℂ)
  have hend : logDeriv xiReading 1 =
      ((1 + Real.eulerMascheroniConstant / 2 -
        Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
    change deriv xiReading 1 / xiReading 1 = _
    exact first_li_coefficient_normalization.1
  have hweighted : HasSum
      (fun n : ℕ => (actualData.multiplicity n : ℂ) *
        (1 / (actualData.zero n * (1 - actualData.zero n))))
      (firstLiMass : ℂ) := by
    convert hres using 1
    · funext n
      have hs := (actualData.zero_isNontrivial n).2
      have h0 : actualData.zero n ≠ 0 := by
        intro he
        have := hs.1
        simpa only [he, Complex.zero_re, lt_self_iff_false] using this
      have h1 : actualData.zero n ≠ 1 := by
        intro he
        have := hs.2
        simpa only [he, Complex.one_re, lt_self_iff_false] using this
      field_simp [h0, sub_ne_zero.mpr h1.symm]
      <;> ring
    · rw [href, hend]
      unfold firstLiMass
      push_cast
      ring
  have hnorm : Summable (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      ‖1 / (actualData.zero n * (1 - actualData.zero n))‖) := by
    simpa [norm_mul] using hweighted.summable.norm
  have hSigmaNorm : Summable (fun p : ActualZeroOccurrence =>
      ‖1 / (actualData.zero p.1 * (1 - actualData.zero p.1))‖) := by
    apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using hnorm
  have hSigma : Summable (fun p : ActualZeroOccurrence =>
      1 / (actualData.zero p.1 * (1 - actualData.zero p.1))) :=
    hSigmaNorm.of_norm
  have hSigmaMass : HasSum (fun p : ActualZeroOccurrence =>
      1 / (actualData.zero p.1 * (1 - actualData.zero p.1))) (firstLiMass : ℂ) := by
    convert hSigma.hasSum using 1
    rw [hSigma.tsum_sigma]
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hweighted.tsum_eq.symm
  have hmass : HasSum a (firstLiMass : ℂ) := by
    simpa only [Function.comp_def, a, actualZero] using
      (actualOccurrenceEquiv.hasSum_iff).2 hSigmaMass
  have hRSigma : Summable (fun p : ActualZeroOccurrence =>
      ((actualData.zero p.1).im)⁻¹ ^ 2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using actual_weighted_inverse_square_summable
  have hR : Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
    simpa only [Function.comp_def, actualZero] using
      (actualOccurrenceEquiv.summable_iff).2 hRSigma
  have hcoeff (k : ℕ) : ‖a k‖ ≤ ((actualZero k).im)⁻¹ ^ 2 := by
    have hheight := actual_height_gt_ten (actualZero k)
      (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    have ht : 0 < |(actualZero k).im| := by linarith
    have ht2 : 0 < (actualZero k).im ^ 2 := by
      have he := sq_pos_of_pos ht
      simpa only [sq_abs] using he
    have hp : |(actualZero k).im| ≤ ‖actualZero k‖ :=
      Complex.abs_im_le_norm _
    have hm : |(actualZero k).im| ≤ ‖1 - actualZero k‖ := by
      simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using
        Complex.abs_im_le_norm (1 - actualZero k)
    have hprod : (actualZero k).im ^ 2 ≤ ‖actualZero k‖ * ‖1 - actualZero k‖ := by
      calc
        _ = |(actualZero k).im| * |(actualZero k).im| := by
          rw [← sq_abs]
          ring
        _ ≤ _ := mul_le_mul hp hm (abs_nonneg _) (norm_nonneg _)
    calc
      ‖a k‖ = 1 / (‖actualZero k‖ * ‖1 - actualZero k‖) := by
        simp only [a, norm_div, norm_one, norm_mul]
      _ ≤ 1 / ((actualZero k).im ^ 2) := one_div_le_one_div_of_le ht2 hprod
      _ = ((actualZero k).im)⁻¹ ^ 2 := by simp only [one_div, inv_pow]
  let σ : Equiv.Perm ActualZeroOccurrence :=
    Equiv.sigmaCongr actualData.conjugation
      (fun n => finCongr (actualData.multiplicity_conjugation n).symm)
  let c : Equiv.Perm ℕ :=
    actualOccurrenceEquiv.trans (σ.trans actualOccurrenceEquiv.symm)
  have hc (k : ℕ) : actualZero (c k) = conj (actualZero k) := by
    simp only [actualZero, c, Equiv.trans_apply, Equiv.apply_symm_apply]
    change actualData.zero (actualData.conjugation (actualOccurrenceEquiv k).1) = _
    exact actualData.zero_conjugation _
  let f : ℝ → ℕ → ℂ := fun y k => a k * Complex.exp ((y : ℂ) * actualZero k)
  have hdom (y : ℝ) (k : ℕ) : ‖f y k‖ ≤ ‖a k‖ * Real.exp (max y 0) := by
    have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
    have hs0 : 0 ≤ (actualZero k).re := hs.1.le
    have hs1 : (actualZero k).re ≤ 1 := hs.2.le
    have he : y * (actualZero k).re ≤ max y 0 := by
      rcases le_or_gt 0 y with hy | hy
      · rw [max_eq_left hy]
        nlinarith
      · have hm : y * (actualZero k).re ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hy.le hs0
        simpa only [max_eq_right hy.le] using hm
    dsimp only [f]
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _)
  have hsum (y : ℝ) : Summable (f y) :=
    Summable.of_norm_bounded (hmass.summable.norm.mul_right (Real.exp (max y 0)))
      (hdom y)
  have hconj (y : ℝ) (k : ℕ) : conj (f y k) = f y (c k) := by
    dsimp only [f, a]
    simp only [map_mul, map_div₀, map_one, map_sub, ← Complex.exp_conj,
      Complex.conj_ofReal, hc]
  have hreal (y : ℝ) : (∑' k : ℕ, f y k).im = 0 := by
    have he : conj (∑' k : ℕ, f y k) = ∑' k : ℕ, f y k := by
      rw [Complex.conj_tsum]
      simp_rw [hconj]
      exact c.tsum_eq (f y)
    have him := congrArg Complex.im he
    simp only [Complex.conj_im] at him
    linarith
  have hbound (y : ℝ) : ‖∑' k : ℕ, f y k‖ ≤
      ((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0) := by
    have hmajor : HasSum
        (fun k : ℕ => (((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0))
        ((∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0)) :=
      hR.hasSum.mul_right _
    calc
      _ ≤ (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0) := by
        apply tsum_of_norm_bounded hmajor
        intro k
        exact (hdom y k).trans
          (mul_le_mul_of_nonneg_right (hcoeff k) (Real.exp_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_right actual_inverse_square_mass_le_height
        (Real.exp_nonneg _)
  have hexchange (w : ℝ → ℂ) (hw : AEStronglyMeasurable w volume)
      (hwi : Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖)) :
      HasSum
        (fun k : ℕ => a k * ∫ y : ℝ,
          Complex.exp ((y : ℂ) * actualZero k) * w y)
        (∫ y : ℝ, (∑' k : ℕ, f y k) * w y) := by
    let F : ℕ → ℝ → ℂ := fun k y => f y k * w y
    let b : ℕ → ℝ → ℝ := fun k y =>
      ‖a k‖ * (Real.exp (max y 0) * ‖w y‖)
    have hF : ∀ k : ℕ, AEStronglyMeasurable (F k) volume := by
      intro k
      have hcontinuous : Continuous (fun y : ℝ => f y k) := by
        dsimp only [f]
        fun_prop
      exact hcontinuous.aestronglyMeasurable.mul hw
    have hFb : ∀ k : ℕ, ∀ᵐ y : ℝ, ‖F k y‖ ≤ b k y := by
      intro k
      exact ae_of_all volume fun y => by
        calc
          _ = ‖f y k‖ * ‖w y‖ := norm_mul _ _
          _ ≤ (‖a k‖ * Real.exp (max y 0)) * ‖w y‖ :=
            mul_le_mul_of_nonneg_right (hdom y k) (norm_nonneg _)
          _ = _ := by dsimp only [b]; ring
    have hbsum : ∀ᵐ y : ℝ, Summable (fun k : ℕ => b k y) :=
      ae_of_all volume fun y =>
        hmass.summable.norm.mul_right (Real.exp (max y 0) * ‖w y‖)
    have hbint : Integrable (fun y : ℝ => ∑' k : ℕ, b k y) := by
      simpa only [b, tsum_mul_right] using
        hwi.const_mul (∑' k : ℕ, ‖a k‖)
    have hlim : ∀ᵐ y : ℝ,
        HasSum (fun k : ℕ => F k y) ((∑' k : ℕ, f y k) * w y) := by
      exact ae_of_all volume fun y => (hsum y).hasSum.mul_right (w y)
    have hd := hasSum_integral_of_dominated_convergence b hF hFb hbsum hbint hlim
    convert hd using 1
    funext k
    dsimp only [F, f]
    simp only [mul_assoc, integral_const_mul]
  exact ⟨hmass, c, hc, (fun y => ⟨hsum y, hreal y, hbound y⟩), hexchange⟩


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

/-- Genuine weighted integrability of K; no m≥1 hypothesis is used here. -/
theorem gaussianK_weighted_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => Real.exp (max y 0) * ‖(gaussianK m γ y : ℂ)‖) := by
  have hw := gaussianW_weighted_integrable m γ hm
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => Real.exp (max y 0) * ‖(gaussianK m γ y : ℂ)‖) volume := by
    have hc : Continuous (fun y : ℝ => Real.exp (max y 0) *
        ‖(gaussianK m γ y : ℂ)‖) := by
      dsimp [gaussianK, gaussianW, gaussianP, gaussianU, gaussianDensity]
      fun_prop
    exact hc.aestronglyMeasurable
  refine hw.mono' hmeas (ae_of_all volume fun y => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  simpa only [gaussianK, Complex.norm_real, Real.norm_eq_abs] using
    Complex.abs_re_le_norm (gaussianW m γ y)

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

/-- Integrability is proved for every complex transform parameter, before evaluation. -/
theorem gaussianW_tilt_integrable (m γ : ℝ) (hm : 0 < m) (ρ : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (ρ * (y : ℂ)) * gaussianW m γ y) := by
  simpa only [gaussianW_tilt_eq] using
    quadraticAt_integrable m γ hm (ρ - Complex.I * γ)

theorem gaussianV_tilt_integrable (m γ : ℝ) (hm : 0 < m) (ρ : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (ρ * (y : ℂ)) *
      (gaussianV m γ y : ℂ)) := by
  simpa only [gaussianV_tilt_eq] using envelopeAt_integrable m γ hm ρ

theorem gaussianK_tilt_integrable (m γ : ℝ) (hm : 0 < m) (ρ : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (ρ * (y : ℂ)) *
      (gaussianK m γ y : ℂ)) := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ =>
      Complex.exp (ρ * (y : ℂ)) * (gaussianK m γ y : ℂ)) volume := by
    have hc : Continuous (fun y : ℝ =>
        Complex.exp (ρ * (y : ℂ)) * (gaussianK m γ y : ℂ)) := by
      dsimp [gaussianK, gaussianW, gaussianP, gaussianU, gaussianDensity]
      fun_prop
    exact hc.aestronglyMeasurable
  refine (gaussianW_tilt_integrable m γ hm ρ).mono hmeas
    (ae_of_all volume fun y => ?_)
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [gaussianK, Complex.norm_real, Real.norm_eq_abs] using
    Complex.abs_re_le_norm (gaussianW m γ y)

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
  obtain ⟨_, _, _, hp, _⟩ := actual_occurrence_mass_symmetry_growth_exchange
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

theorem H_weighted_K_complex_product_integrable (m γ : ℝ) (hm : 0 < m) :
    Integrable (fun y : ℝ => H y * (gaussianK m γ y : ℂ)) := by
  have hc : Continuous (fun y : ℝ => (gaussianK m γ y : ℂ)) := by
    unfold gaussianK gaussianW gaussianP gaussianU gaussianDensity
    fun_prop
  exact H_mul_weight_integrable _ hc.aestronglyMeasurable
    (gaussianK_weighted_integrable m γ hm)

private theorem H_im_zero (y : ℝ) : (H y).im = 0 := by
  obtain ⟨_, _, _, hp, _⟩ := actual_occurrence_mass_symmetry_growth_exchange
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
  obtain ⟨_, _, _, _, hex⟩ := actual_occurrence_mass_symmetry_growth_exchange
  have hcW : Continuous (gaussianW m γ) := by
    unfold gaussianW gaussianP gaussianU gaussianDensity
    fun_prop
  have he := hex (gaussianW m γ) hcW.aestronglyMeasurable
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
  obtain ⟨_, _, _, _, hex⟩ := actual_occurrence_mass_symmetry_growth_exchange
  have hcV : Continuous (fun y : ℝ => (gaussianV m γ y : ℂ)) := by
    dsimp [gaussianV, gaussianU, gaussianDensity]
    fun_prop
  have he := hex (fun y : ℝ => (gaussianV m γ y : ℂ))
    hcV.aestronglyMeasurable (gaussianV_weighted_integrable m γ hm)
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

/-- The entire envelope response, with its factor two outside the real part.
The reciprocal coefficient remains complex and every occurrence is retained. -/
theorem actual_signed_V_real_exchange (m γ : ℝ) (hm : 0 < m) :
    (∫ y : ℝ, (H y).re * gaussianV m γ y) =
      2 * (∑' k : ℕ,
        (1 / (actualZero k * (1 - actualZero k))) *
          (actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) *
          Complex.exp ((m : ℂ) * actualZero k ^ 2 +
            (16 * (m : ℂ)) * actualZero k)).re := by
  have hsum := actual_signed_V_exchange m γ hm
  have hI := H_weighted_V_product_integrable m γ hm
  calc
    (∫ y : ℝ, (H y).re * gaussianV m γ y) =
        ∫ y : ℝ, (H y * (gaussianV m γ y : ℂ)).re := by
      apply integral_congr_ae
      exact ae_of_all volume fun y => by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
    _ = (∫ y : ℝ, H y * (gaussianV m γ y : ℂ)).re := integral_re hI
    _ = (∑' k : ℕ,
        (1 / (actualZero k * (1 - actualZero k))) *
          (2 * (actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) *
            Complex.exp ((m : ℂ) * actualZero k ^ 2 +
              (16 * (m : ℂ)) * actualZero k))).re := by rw [hsum.tsum_eq]
    _ = (2 * ∑' k : ℕ,
        (1 / (actualZero k * (1 - actualZero k))) *
          (actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) *
          Complex.exp ((m : ℂ) * actualZero k ^ 2 +
            (16 * (m : ℂ)) * actualZero k)).re := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = _ := by simp

/-- An absolute exchange for the actual occurrence family. Each summand is
integrable, the sum of its absolute values is integrable, and the integrals
of those absolute values have the indicated finite sum. W, K and v satisfy
these hypotheses by the proved weighted integrability theorems above. -/
theorem actual_absolute_exchange (w : ℝ → ℂ) (hw : Continuous w)
    (hwi : Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖)) :
    let F : ℕ → ℝ → ℂ := fun k y =>
      (1 / (actualZero k * (1 - actualZero k))) *
        Complex.exp ((y : ℂ) * actualZero k) * w y
    (∀ k : ℕ, Integrable (F k)) ∧
      Integrable (fun y : ℝ => ∑' k : ℕ, ‖F k y‖) ∧
      HasSum (fun k : ℕ => ∫ y : ℝ, ‖F k y‖)
        (∫ y : ℝ, ∑' k : ℕ, ‖F k y‖) := by
  classical
  dsimp only
  let a : ℕ → ℂ := fun k => 1 / (actualZero k * (1 - actualZero k))
  let F : ℕ → ℝ → ℂ := fun k y =>
    a k * Complex.exp ((y : ℂ) * actualZero k) * w y
  let B : ℝ → ℝ := fun y => Real.exp (max y 0) * ‖w y‖
  obtain ⟨hmass, _, _, _, _⟩ := actual_occurrence_mass_symmetry_growth_exchange
  have ha : Summable (fun k : ℕ => ‖a k‖) := hmass.summable.norm
  have hFcont (k : ℕ) : Continuous (F k) := by
    dsimp only [F]
    exact (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))).mul hw
  have hdom (y : ℝ) (k : ℕ) : ‖F k y‖ ≤ ‖a k‖ * B y := by
    have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
    have hs0 : 0 ≤ (actualZero k).re := hs.1.le
    have hs1 : (actualZero k).re ≤ 1 := hs.2.le
    have he : y * (actualZero k).re ≤ max y 0 := by
      rcases le_or_gt 0 y with hy | hy
      · rw [max_eq_left hy]
        nlinarith
      · have ht : y * (actualZero k).re ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hy.le hs0
        simpa only [max_eq_right hy.le] using ht
    dsimp only [F, B]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    calc
      ‖a k‖ * Real.exp (y * (actualZero k).re) * ‖w y‖ ≤
          ‖a k‖ * Real.exp (max y 0) * ‖w y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  have hFi (k : ℕ) : Integrable (F k) :=
    (hwi.const_mul ‖a k‖).mono' (hFcont k).aestronglyMeasurable
      (ae_of_all volume fun y => hdom y k)
  have hns (y : ℝ) : Summable (fun k : ℕ => ‖F k y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hdom y) (ha.mul_right (B y))
  have hsummeas : AEStronglyMeasurable (fun y : ℝ => ∑' k : ℕ, ‖F k y‖) volume :=
    (Measurable.tsum (fun k => (hFcont k).norm.measurable)).aestronglyMeasurable
  have hsumdom (y : ℝ) : (∑' k : ℕ, ‖F k y‖) ≤ (∑' k : ℕ, ‖a k‖) * B y := by
    calc
      _ ≤ ∑' k : ℕ, ‖a k‖ * B y :=
        (hns y).tsum_le_tsum (hdom y) (ha.mul_right (B y))
      _ = _ := tsum_mul_right
  have hsumI : Integrable (fun y : ℝ => ∑' k : ℕ, ‖F k y‖) := by
    refine (hwi.const_mul (∑' k : ℕ, ‖a k‖)).mono' hsummeas
      (ae_of_all volume fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
    exact hsumdom y
  have hbsum : ∀ᵐ y : ℝ, Summable (fun k : ℕ => ‖a k‖ * B y) :=
    ae_of_all volume fun y => ha.mul_right (B y)
  have hbI : Integrable (fun y : ℝ => ∑' k : ℕ, ‖a k‖ * B y) := by
    simpa only [tsum_mul_right, B] using hwi.const_mul (∑' k : ℕ, ‖a k‖)
  have habs : HasSum (fun k : ℕ => ∫ y : ℝ, ‖F k y‖)
      (∫ y : ℝ, ∑' k : ℕ, ‖F k y‖) := by
    apply hasSum_integral_of_dominated_convergence (fun k y => ‖a k‖ * B y)
      (fun k => (hFcont k).norm.aestronglyMeasurable) ?_ hbsum hbI
      (ae_of_all volume fun y => (hns y).hasSum)
    intro k
    exact ae_of_all volume fun y => by simpa only [norm_norm] using hdom y k
  exact ⟨hFi, hsumI, habs⟩


end D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange

end
