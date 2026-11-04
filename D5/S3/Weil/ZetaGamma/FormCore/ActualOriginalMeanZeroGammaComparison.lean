/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualOriginalMeanZeroGammaComparison
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-original-gamma-comparison)
   anchors: []
   utility: none
   digest: Original mean-zero Gamma comparison and genuine even-energy integrability. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace
import D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! The original mean-zero source controls the literal Gamma energy difference. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open scoped ENNReal Topology ComplexConjugate

private def originalGammaCubicCoefficient (n : ℕ) : ℝ :=
  ((((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹

private def originalGammaCubicSeries : ℝ :=
  ∑' n : ℕ, originalGammaCubicCoefficient n

/- Actual cubic dilation series: direct public Mathlib rpow/integral-test APIs. -/
private theorem original_gamma_cubic_series_bounds :
    0 ≤ originalGammaCubicSeries ∧ originalGammaCubicSeries ≤ 11 / 9 := by
  let g : ℝ → ℝ := fun x => x ^ (-3 : ℝ)
  have hgi : IntegrableOn g (Ioi (3 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hgm : (∫ x : ℝ in Ioi 3, g x) = 1 / 18 := by
    dsimp [g]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num)]
    norm_num [Real.rpow_neg_ofNat]
  have hga : AntitoneOn g (Ici (3 : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [show (3 : ℝ) ≤ x from hx])
      hxy (by norm_num)
  have hgn : ∀ x ∈ Ioi (3 : ℝ), 0 ≤ g x := by
    intro x hx
    exact Real.rpow_nonneg (by linarith [show (3 : ℝ) < x from hx]) _
  have hgs : Summable (fun n : ℕ => g n) := hga.summable_of_integrableOn_Ioi hgi hgn
  have hc (n : ℕ) : originalGammaCubicCoefficient n = g (n + 1 : ℕ) := by
    norm_num [originalGammaCubicCoefficient, g, Real.rpow_neg_ofNat]
  have hcs : Summable originalGammaCubicCoefficient :=
    ((summable_nat_add_iff 1).2 hgs).congr fun n => (hc n).symm
  have htail : (∑' n : ℕ, originalGammaCubicCoefficient (n + 3)) ≤ 1 / 18 := by
    have h := AntitoneOn.tsum_comp_add_le_integral 3 hga hgi hgn
    norm_num only [Nat.cast_ofNat] at h
    rw [hgm] at h
    have heq : (∑' n : ℕ, originalGammaCubicCoefficient (n + 3)) =
        ∑' n : ℕ, g (n + 3 + 1 : ℕ) := tsum_congr fun n => hc (n + 3)
    rw [heq]
    exact h
  refine ⟨tsum_nonneg (fun n => by unfold originalGammaCubicCoefficient; positivity), ?_⟩
  unfold originalGammaCubicSeries
  rw [← hcs.sum_add_tsum_nat_add 3]
  have hp : (∑ n ∈ Finset.range 3, originalGammaCubicCoefficient n) =
      (1 : ℝ) + 1 / 8 + 1 / 27 := by
    norm_num [Finset.sum_range_succ, originalGammaCubicCoefficient]
  rw [hp]
  linarith

/- Finite debit consumes the actual strongest original-source moment theorem. -/
private theorem actual_gamma_finite_correction_from_actual_moments
    {A P D : ℝ} {L0 Lt : ℂ}
    (hA : -(49 / 100 : ℝ) < A)
    (h0 : ‖L0‖ ^ 2 ≤ (3 / 1000 : ℝ) * P * D)
    (hprod : ‖L0‖ * ‖Lt‖ ≤ (3 / 400 : ℝ) * P * D) :
    -(1047 / 100000 : ℝ) * P * D ≤
      A * ‖L0‖ ^ 2 - (6 / 5 : ℝ) * (conj L0 * Lt).re := by
  have hRe : (conj L0 * Lt).re ≤ (3 / 400 : ℝ) * P * D := by
    calc
      _ ≤ ‖conj L0 * Lt‖ := Complex.re_le_norm _
      _ = ‖L0‖ * ‖Lt‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := hprod
  have hCoeff : -(49 / 100 : ℝ) * ‖L0‖ ^ 2 ≤ A * ‖L0‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hA.le (sq_nonneg _)
  have h0pay : -(49 / 100 : ℝ) * ((3 / 1000 : ℝ) * P * D) ≤
      -(49 / 100 : ℝ) * ‖L0‖ ^ 2 :=
    mul_le_mul_of_nonpos_left h0 (by norm_num)
  calc
    _ = -(49 / 100 : ℝ) * ((3 / 1000 : ℝ) * P * D) -
        (6 / 5 : ℝ) * ((3 / 400 : ℝ) * P * D) := by ring
    _ ≤ -(49 / 100 : ℝ) * ‖L0‖ ^ 2 -
        (6 / 5 : ℝ) * (conj L0 * Lt).re :=
      sub_le_sub h0pay (mul_le_mul_of_nonneg_left hRe (by norm_num))
    _ ≤ _ := sub_le_sub_right hCoeff _

private theorem original_gamma_pi_seven_halves :
    Real.pi ^ (7 / 2 : ℝ) = Real.pi ^ (3 : ℕ) * Real.sqrt Real.pi := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast Real.pi 3,
    ← Real.rpow_add Real.pi_pos]
  norm_num

private theorem original_gamma_absorption_coefficient :
    (1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ) *
      originalGammaCubicSeries ^ 2 < 1 / 2 := by
  obtain ⟨hz0, hz⟩ := original_gamma_cubic_series_bounds
  have hp : Real.pi ≤ (63 / 20 : ℝ) := by linarith [Real.pi_lt_d2]
  have hp3 := pow_le_pow_left₀ Real.pi_pos.le hp 3
  have hz2 := pow_le_pow_left₀ hz0 hz 2
  have hfirst : (1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ) ≤
      (1047 / 100000 : ℝ) * (63 / 20 : ℝ) ^ (3 : ℕ) :=
    mul_le_mul_of_nonneg_left hp3 (by norm_num)
  have hboth := mul_le_mul hfirst hz2 (sq_nonneg originalGammaCubicSeries)
    (by positivity : (0 : ℝ) ≤ (1047 / 100000 : ℝ) * (63 / 20 : ℝ) ^ (3 : ℕ))
  exact lt_of_le_of_lt hboth (by norm_num)

private def originalGammaExcess (F : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2

private theorem original_gamma_excess_nonneg (F : ℝ → ℂ) :
    0 ≤ originalGammaExcess F := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpi : 1 ≤ x / Real.pi :=
    (le_div_iff₀ Real.pi_pos).2 (by simpa only [one_mul] using hx.le)
  exact mul_nonneg (sub_nonneg.2 (one_le_pow₀ hxpi)) (sq_nonneg _)

private def originalGammaLaplaceZero (F : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * actualGammaProfile F t

private def originalGammaLaplaceFirst (F : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) * actualGammaProfile F t

private def originalGammaFiniteCoefficient : ℝ :=
  64 / 25 + (6 / 5) * ((Complex.digamma 1).re - Real.log (2 * Real.pi))

/- The original-source moments bound the finite part of the Gamma energy. -/
private theorem actual_original_mean_zero_gamma_excess_from_finite_kernel
    (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hmean : (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0)
    (DeltaGamma : ℝ)
    (hA : -(49 / 100 : ℝ) < originalGammaFiniteCoefficient)
    (hFinite :
      (originalGammaFiniteCoefficient * ‖originalGammaLaplaceZero F‖ ^ 2 -
        (6 / 5 : ℝ) *
          (conj (originalGammaLaplaceZero F) * originalGammaLaplaceFirst F).re) /
            Real.sqrt Real.pi ≤ DeltaGamma) :
    -(originalGammaExcess F) / 2 ≤ DeltaGamma := by
  obtain ⟨_, _, h0, _, hprod⟩ := actual_h6_mean_zero_physical_moment_bounds F hF hmean
  have h0' : ‖originalGammaLaplaceZero F‖ ^ 2 ≤
      (3 / 1000 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * originalGammaExcess (fullTheta F) := by
    simpa only [originalGammaLaplaceZero, originalGammaExcess] using h0
  have hprod' : ‖originalGammaLaplaceZero F‖ * ‖originalGammaLaplaceFirst F‖ ≤
      (3 / 400 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * originalGammaExcess (fullTheta F) := by
    simpa only [originalGammaLaplaceZero, originalGammaLaplaceFirst, originalGammaExcess] using hprod
  have hDF := original_gamma_excess_nonneg F
  have hCorr := actual_gamma_finite_correction_from_actual_moments hA h0' hprod'
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hRaw : -(1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ) *
      originalGammaExcess (fullTheta F) ≤ DeltaGamma := by
    calc
      _ = (-(1047 / 100000 : ℝ) * Real.pi ^ (7 / 2 : ℝ) *
          originalGammaExcess (fullTheta F)) / Real.sqrt Real.pi := by
        rw [original_gamma_pi_seven_halves]
        field_simp [hs.ne']
      _ ≤ _ := (div_le_div_of_nonneg_right hCorr hs.le).trans hFinite
  have hTheta : originalGammaExcess (fullTheta F) ≤
      originalGammaCubicSeries ^ 2 * originalGammaExcess F := by
    simpa only [originalGammaExcess, originalGammaCubicSeries,
      originalGammaCubicCoefficient] using (actual_h6_fullTheta_excess_bound F hF).2.2
  have hThetaPay := mul_le_mul_of_nonneg_left hTheta
    (by positivity : (0 : ℝ) ≤ (1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ))
  have hAbsorb := mul_le_mul_of_nonneg_right
    original_gamma_absorption_coefficient.le hDF
  calc
    -(originalGammaExcess F) / 2 = -((1 / 2 : ℝ) * originalGammaExcess F) := by ring
    _ ≤ -(((1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ) *
        originalGammaCubicSeries ^ 2) * originalGammaExcess F) := neg_le_neg hAbsorb
    _ = -(((1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ)) *
        (originalGammaCubicSeries ^ 2 * originalGammaExcess F)) := by ring
    _ ≤ -(((1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ)) *
        originalGammaExcess (fullTheta F)) := neg_le_neg hThetaPay
    _ = -(1047 / 100000 : ℝ) * Real.pi ^ (3 : ℕ) *
        originalGammaExcess (fullTheta F) := by ring
    _ ≤ DeltaGamma := hRaw

open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
open D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross

private theorem original_log_two_pi_lt_fifteen_eighths :
    Real.log (2 * Real.pi) < 15 / 8 := by
  rw [Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have he : (1688089 / 262144 : ℝ) ≤ Real.exp (15 / 8) := by
    convert (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 8) 6) using 1 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  linarith [Real.pi_lt_d2]

private theorem original_gamma_finite_coefficient_lower :
    -(49 / 100 : ℝ) < originalGammaFiniteCoefficient := by
  unfold originalGammaFiniteCoefficient
  rw [Complex.digamma_one]
  simp only [Complex.neg_re, Complex.ofReal_re]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds,
    original_log_two_pi_lt_fifteen_eighths]

private def originalGammaEnergyDifference (c : ℝ) (F : ℝ → ℂ) : ℝ :=
  (∫ ξ : ℝ, (gammaWeight ξ + c) * ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2) -
    (∫ ξ : ℝ, (gammaWeight ξ + c) *
      ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile F |t|) ξ‖ ^ 2) / 2

private theorem actual_original_gamma_finite_debit
    (c : ℝ) (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hGamma : originalGammaFormDomain c F) :
    Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile F |t|) ξ‖ ^ 2) volume ∧
    (originalGammaFiniteCoefficient * ‖originalGammaLaplaceZero F‖ ^ 2 -
      (6 / 5 : ℝ) *
        (conj (originalGammaLaplaceZero F) * originalGammaLaplaceFirst F).re) /
          Real.sqrt Real.pi ≤ originalGammaEnergyDifference c F := by
  obtain ⟨hu₁, hu₂⟩ := actual_h6_gamma_profile_l1_l2 F hF
  have hAE : (Ioi (0 : ℝ)).indicator (actualGammaProfile F) =ᵐ[volume]
      actualGammaProfile F := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    by_cases hp : 0 < t
    · exact Set.indicator_of_mem hp _
    · have hn : ¬0 ≤ t := by
        intro hnonneg
        exact ht (le_antisymm (le_of_not_gt hp) hnonneg)
      rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from hp)
        (actualGammaProfile F)]
      simp only [actualGammaProfile, if_neg hn]
  have hFourier (ξ : ℝ) :
      unitarySourceFourier ((Ioi (0 : ℝ)).indicator (actualGammaProfile F)) ξ =
        unitarySourceFourier (actualGammaProfile F) ξ := by
    simp only [unitarySourceFourier, Real.fourier_congr_ae hAE]
  have hG : Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier ((Ioi (0 : ℝ)).indicator (actualGammaProfile F)) ξ‖ ^ 2)
        volume := by
    simpa only [originalGammaFormDomain, hFourier] using hGamma
  obtain ⟨_, hEven, hExact⟩ :=
    actual_gamma_literal_even_difference_positive_tail_and_resonance c hu₁ hu₂ hG
  have hL0 : literalSourceLaplace (5 / 4) (actualGammaProfile F) =
      originalGammaLaplaceZero F := rfl
  have hLt : literalSourceFirstLaplaceMoment (5 / 4) (actualGammaProfile F) =
      originalGammaLaplaceFirst F := by
    simp only [literalSourceFirstLaplaceMoment, originalGammaLaplaceFirst,
      Complex.ofReal_mul]
  change Real.sqrt Real.pi *
      ((∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier ((Ioi (0 : ℝ)).indicator (actualGammaProfile F)) ξ‖ ^ 2) -
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile F |t|) ξ‖ ^ 2) / 2) =
      (∑' n : ℕ, actualGammaPositiveTailTerm (actualGammaProfile F) n) +
        ((64 / 25 : ℝ) + (6 / 5) * ((Complex.digamma 1).re - Real.log (2 * Real.pi))) *
          Complex.normSq (literalSourceLaplace (5 / 4) (actualGammaProfile F)) -
        (6 / 5) * ((starRingEnd ℂ) (literalSourceLaplace (5 / 4) (actualGammaProfile F)) *
          literalSourceFirstLaplaceMoment (5 / 4) (actualGammaProfile F)).re at hExact
  have hEq : Real.sqrt Real.pi * originalGammaEnergyDifference c F =
      (∑' n : ℕ, actualGammaPositiveTailTerm (actualGammaProfile F) n) +
        originalGammaFiniteCoefficient * ‖originalGammaLaplaceZero F‖ ^ 2 -
        (6 / 5 : ℝ) *
          (conj (originalGammaLaplaceZero F) * originalGammaLaplaceFirst F).re := by
    simpa only [originalGammaEnergyDifference, hFourier, hL0, hLt,
      Complex.normSq_eq_norm_sq, originalGammaFiniteCoefficient] using hExact
  have hTail : 0 ≤ ∑' n : ℕ, actualGammaPositiveTailTerm (actualGammaProfile F) n := by
    apply tsum_nonneg
    intro n
    unfold actualGammaPositiveTailTerm
    apply mul_nonneg
    · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      positivity
    · exact Complex.normSq_nonneg _
  refine ⟨hEven, (div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)).2 ?_⟩
  rw [mul_comm (originalGammaEnergyDifference c F) (Real.sqrt Real.pi), hEq]
  linarith only [hTail]

/-- Original mean-zero comparison on the SAME original H6 input and its
actual Gamma graph. H6 pays profile L1/L2; the exact complete Gamma identity
pays the finite debit. The even profile has genuine finite shifted-Gamma
energy. No finite-kernel or trace-zero premise remains. -/
theorem actual_original_mean_zero_gamma_excess_comparison
    (c : ℝ) (F : ℝ → ℂ) (hF : originalPhysicalH6 F)
    (hmean : (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0)
    (hGamma : originalGammaFormDomain c F) :
    Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile F |t|) ξ‖ ^ 2) volume ∧
    -(∫ x : ℝ in Ioi Real.pi,
        ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2) / 2 ≤
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2) -
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (fun t : ℝ => actualGammaProfile F |t|) ξ‖ ^ 2) / 2 := by
  obtain ⟨hEven, hFinite⟩ := actual_original_gamma_finite_debit c F hF hGamma
  refine ⟨hEven, ?_⟩
  simpa only [originalGammaExcess, originalGammaEnergyDifference] using
    actual_original_mean_zero_gamma_excess_from_finite_kernel F hF hmean
      (originalGammaEnergyDifference c F) original_gamma_finite_coefficient_lower hFinite


end D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma
