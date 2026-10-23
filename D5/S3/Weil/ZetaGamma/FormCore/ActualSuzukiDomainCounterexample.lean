/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-domain-refutation)
   anchors: []
   utility: none
   digest: Sharp sixth-moment threshold for simultaneous actual Gamma-domain escape. -/

import D5.S3.Weil.ZetaCore.PaperFT
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import D5.S3.Weil.ZetaGamma.GammaMu
import D5.S3.Weil.ZetaGamma.GammaStirlingVert

/-!
An explicit real physical source has arbitrarily small excess sixth moment
and divergent positive-log Fourier energy for its actual full-theta profile.
For every K>1, one compressed source escapes all constant shifts of the
literal Gamma weight that remain at least one.
-/


noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

def tent (s : ℝ) : ℝ := max (1 - 4 * |s|) 0
def coeff (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)
def frequency (n : ℕ) : ℝ := Real.exp ((4 : ℝ) ^ (n + 1))
def carrierSeries (t : ℝ) : ℝ :=
  ∑' n : ℕ, coeff n * Real.cos (frequency n * (t - 1 / 2))
def counterProfileReal (t : ℝ) : ℝ := tent (t - 1 / 2) * carrierSeries t
def counterProfile (t : ℝ) : ℂ := (counterProfileReal t : ℂ)

private theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  unfold coeff
  positivity

private theorem coeff_hasSum : HasSum coeff 1 := by
  have h := (hasSum_geometric_of_abs_lt_one
    (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left (1 / 2 : ℝ)
  convert h using 1
  · funext n
    dsimp [coeff]
    rw [pow_succ]
    ring
  · norm_num

private theorem carrierTerm_norm_le (n : ℕ) (t : ℝ) :
    ‖coeff n * Real.cos (frequency n * (t - 1 / 2))‖ ≤ coeff n := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (coeff_nonneg n)]
  exact mul_le_of_le_one_right (coeff_nonneg n) (Real.abs_cos_le_one _)

private theorem carrierSeries_continuous : Continuous carrierSeries := by
  exact continuous_tsum (fun n => by fun_prop) coeff_hasSum.summable
    carrierTerm_norm_le

private theorem tent_continuous : Continuous tent := by
  unfold tent
  fun_prop

private theorem tent_nonneg (s : ℝ) : 0 ≤ tent s := le_max_right _ _

private theorem tent_zero_of_quarter_le {s : ℝ} (hs : 1 / 4 ≤ |s|) :
    tent s = 0 := by
  apply max_eq_right
  linarith

private theorem profile_continuous : Continuous counterProfile := by
  have h : Continuous counterProfileReal :=
    (tent_continuous.comp (continuous_id.sub continuous_const)).mul
      carrierSeries_continuous
  exact Complex.continuous_ofReal.comp h

private theorem profile_zero_off {t : ℝ}
    (ht : t ∉ Icc (1 / 4 : ℝ) (3 / 4)) : counterProfile t = 0 := by
  have hs : (1 / 4 : ℝ) ≤ |t - 1 / 2| := by
    by_contra h
    have ha := abs_lt.mp (lt_of_not_ge h)
    apply ht
    constructor <;> linarith [ha.1, ha.2]
  simp only [counterProfile, counterProfileReal, tent_zero_of_quarter_le hs,
    zero_mul, Complex.ofReal_zero]

private theorem profile_center : counterProfile (1 / 2) = 1 := by
  have h : carrierSeries (1 / 2) = 1 := by
    simpa only [carrierSeries, sub_self, mul_zero, Real.cos_zero, mul_one] using
      coeff_hasSum.tsum_eq
  simp only [counterProfile, counterProfileReal, h]
  norm_num [tent]

def sourceOfProfile (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  if Real.pi ≤ x then ((x ^ (-9 / 4 : ℝ) : ℝ) : ℂ) * u (Real.log (x / Real.pi))
  else 0

def physicalTerm (F : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (((k + 1 : ℕ) : ℂ) ^ (4 : ℕ)) * F ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * x)

def fullTheta (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℕ, physicalTerm F k x

def actualGammaProfile (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  if 0 ≤ t then
    (((Real.pi * Real.exp t) ^ (9 / 4 : ℝ) : ℝ) : ℂ) *
      fullTheta F (Real.pi * Real.exp t)
  else 0

private theorem three_quarters_lt_log_four : (3 / 4 : ℝ) < Real.log 4 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mpr
  exact lt_trans
    (lt_of_le_of_lt (Real.exp_le_exp.mpr (by norm_num : (3 / 4 : ℝ) ≤ 1))
      Real.exp_one_lt_three) (by norm_num)

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

/- The concrete lacunary source has an explicit nonnegative spectral amplitude.
Its actual Fourier identity is obtained below from tent convolution, cosine
modulation, translation, and dominated series interchange. -/

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set
open scoped FourierTransform Function

/-- The paper's plus-sign unitary transform on the line, represented by
Mathlib's cycles-frequency raw Fourier transform at -ξ/(2*pi), with the exact
amplitude factor 1/sqrt(2*pi). Equivalently its actual integrand is
exp(I*ξ*t)*u(t)/sqrt(2*pi). This single consumed definition fixes the convention;
no separate normalization wrapper or Fourier-identity premise is introduced. -/
def unitarySourceFourier (u : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹ *
    𝓕 u (-ξ / (2 * Real.pi))

private def tentSourceHat (ξ : ℝ) : ℝ :=
  (1 / (4 * Real.sqrt (2 * Real.pi))) * Real.sinc (ξ / 8) ^ 2

private def spectralTerm (n : ℕ) (ξ : ℝ) : ℝ :=
  (coeff n / 2) *
    (tentSourceHat (ξ - frequency n) + tentSourceHat (ξ + frequency n))

private def spectralAmplitude (ξ : ℝ) : ℝ := ∑' n : ℕ, spectralTerm n ξ

private def positiveBand (n : ℕ) : Set ℝ :=
  Icc (frequency n - 1) (frequency n + 1)

private theorem coeff_positive (n : ℕ) : 0 < coeff n := by
  dsimp [coeff]
  positivity

private theorem summable_coefficients : Summable coeff :=
  coeff_hasSum.summable

private theorem log_frequency (n : ℕ) :
    Real.log (frequency n) = (4 : ℝ) ^ (n + 1) := by
  simp [frequency]

private theorem frequency_exponent_ge_four (n : ℕ) :
    (4 : ℝ) ≤ (4 : ℝ) ^ (n + 1) := by
  have hn : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  nlinarith [hn]

private theorem frequency_ge_five (n : ℕ) : 5 ≤ frequency n := by
  have he := Real.add_one_le_exp ((4 : ℝ) ^ (n + 1))
  dsimp [frequency]
  linarith [he, frequency_exponent_ge_four n]

private theorem frequency_gap (n : ℕ) : frequency n + 2 < frequency (n + 1) := by
  let q : ℝ := (4 : ℝ) ^ (n + 1)
  have hq : 4 ≤ q := frequency_exponent_ge_four n
  have hnext : frequency (n + 1) = frequency n * Real.exp (3 * q) := by
    dsimp [frequency, q]
    rw [show (4 : ℝ) ^ (n + 1 + 1) =
      (4 : ℝ) ^ (n + 1) + 3 * (4 : ℝ) ^ (n + 1) by rw [pow_succ]; ring,
      Real.exp_add]
  have hexp : 13 ≤ Real.exp (3 * q) := by
    linarith [Real.add_one_le_exp (3 * q)]
  have hfreq : 0 ≤ frequency n := (frequency_ge_five n).trans' (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hexp hfreq
  rw [← hnext] at hmul
  nlinarith [frequency_ge_five n, hmul]

private theorem frequency_strictMono : StrictMono frequency := by
  apply strictMono_nat_of_lt_succ
  intro n
  linarith [frequency_gap n]

private theorem positiveBands_disjoint : Pairwise (Disjoint on positiveBand) := by
  have hforward (n m : ℕ) (hlt : n < m) :
      Disjoint (positiveBand n) (positiveBand m) := by
    have hstep : n + 1 ≤ m := Nat.succ_le_iff.mpr hlt
    have hfreq := frequency_strictMono.monotone hstep
    apply Set.disjoint_left.2
    intro ξ hn hm
    change ξ ∈ Icc (frequency n - 1) (frequency n + 1) at hn
    change ξ ∈ Icc (frequency m - 1) (frequency m + 1) at hm
    linarith [hn.2, hm.1, frequency_gap n, hfreq]
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hforward n m hlt
  · exact (hforward m n hgt).symm

private theorem coeff_sq_log_frequency (n : ℕ) :
    coeff n ^ 2 * Real.log (frequency n) = 1 := by
  rw [log_frequency]
  dsimp [coeff]
  calc
    ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 * (4 : ℝ) ^ (n + 1) =
        ((1 / 2 : ℝ) ^ 2) ^ (n + 1) * (4 : ℝ) ^ (n + 1) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (n + 1) 2]
    _ = (((1 / 2 : ℝ) ^ 2) * 4) ^ (n + 1) := by rw [mul_pow]
    _ = 1 := by norm_num

private theorem tentSourceHat_nonneg (ξ : ℝ) : 0 ≤ tentSourceHat ξ := by
  dsimp [tentSourceHat]
  positivity

private theorem tentSourceHat_upper (ξ : ℝ) :
    tentSourceHat ξ ≤ 1 / (4 * Real.sqrt (2 * Real.pi)) := by
  have hsinc := abs_le.mp (Real.abs_sinc_le_one (ξ / 8))
  have hsq : Real.sinc (ξ / 8) ^ 2 ≤ 1 := by nlinarith [hsinc.1, hsinc.2]
  exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans_eq (mul_one _)

private theorem tentSourceHat_lower_unit {ξ : ℝ} (hξ : |ξ| ≤ 1) :
    1 / (16 * Real.sqrt (2 * Real.pi)) ≤ tentSourceHat ξ := by
  have hξsq : ξ ^ 2 ≤ 1 := by
    calc
      ξ ^ 2 = |ξ| ^ 2 := (sq_abs ξ).symm
      _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg ξ) hξ 2
      _ = 1 := by norm_num
  have harg : |ξ / 8| < Real.pi / 2 := by
    rw [abs_div, show |(8 : ℝ)| = 8 by norm_num]
    have hπ := Real.pi_gt_three
    linarith [hξ, hπ]
  have hsinc := Real.cos_le_sinc harg
  have hcos := Real.one_sub_sq_div_two_le_cos (x := ξ / 8)
  have hhalf : (1 / 2 : ℝ) ≤ Real.sinc (ξ / 8) := by
    nlinarith [hsinc, hcos, hξsq]
  have hsq : (1 / 4 : ℝ) ≤ Real.sinc (ξ / 8) ^ 2 := by nlinarith [hhalf]
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  calc
    1 / (16 * Real.sqrt (2 * Real.pi)) =
        (1 / (4 * Real.sqrt (2 * Real.pi))) * (1 / 4) := by
      field_simp [hs.ne']
      <;> ring
    _ ≤ tentSourceHat ξ := mul_le_mul_of_nonneg_left hsq (by positivity)

private theorem spectralTerm_nonneg (n : ℕ) (ξ : ℝ) : 0 ≤ spectralTerm n ξ := by
  exact mul_nonneg (div_nonneg (coeff_positive n).le (by norm_num))
    (add_nonneg (tentSourceHat_nonneg _) (tentSourceHat_nonneg _))

private theorem spectralTerm_upper (n : ℕ) (ξ : ℝ) :
    spectralTerm n ξ ≤ coeff n * (1 / (4 * Real.sqrt (2 * Real.pi))) := by
  have hsum := add_le_add (tentSourceHat_upper (ξ - frequency n))
    (tentSourceHat_upper (ξ + frequency n))
  have hmul := mul_le_mul_of_nonneg_left hsum
    (div_nonneg (coeff_nonneg n) (by norm_num : (0 : ℝ) ≤ 2))
  dsimp [spectralTerm]
  nlinarith [hmul]

private theorem spectralTerm_summable (ξ : ℝ) : Summable (fun n => spectralTerm n ξ) :=
  Summable.of_nonneg_of_le (fun n => spectralTerm_nonneg n ξ)
    (fun n => spectralTerm_upper n ξ)
    (summable_coefficients.mul_right (1 / (4 * Real.sqrt (2 * Real.pi))))

private theorem spectralTerm_le_amplitude (n : ℕ) (ξ : ℝ) :
    spectralTerm n ξ ≤ spectralAmplitude ξ :=
  (spectralTerm_summable ξ).le_tsum n (fun m _ => spectralTerm_nonneg m ξ)

private theorem spectralAmplitude_band_lower (n : ℕ) {ξ : ℝ}
    (hξ : ξ ∈ positiveBand n) :
    coeff n / (32 * Real.sqrt (2 * Real.pi)) ≤ spectralAmplitude ξ := by
  have hdist : |ξ - frequency n| ≤ 1 := by
    apply abs_le.mpr
    change ξ ∈ Icc (frequency n - 1) (frequency n + 1) at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  have hpulse := tentSourceHat_lower_unit hdist
  have hother := tentSourceHat_nonneg (ξ + frequency n)
  have hmul := mul_le_mul_of_nonneg_left hpulse
    (div_nonneg (coeff_nonneg n) (by norm_num : (0 : ℝ) ≤ 2))
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hterm : coeff n / (32 * Real.sqrt (2 * Real.pi)) ≤ spectralTerm n ξ := by
    dsimp [spectralTerm]
    have hbase : coeff n / (32 * Real.sqrt (2 * Real.pi)) =
        (coeff n / 2) * (1 / (16 * Real.sqrt (2 * Real.pi))) := by
      field_simp [hs.ne']
      <;> ring
    rw [hbase]
    have hnonneg := mul_nonneg
      (div_nonneg (coeff_nonneg n) (by norm_num : (0 : ℝ) ≤ 2)) hother
    nlinarith [hmul, hnonneg]
  exact hterm.trans (spectralTerm_le_amplitude n ξ)

private theorem positiveBand_log_lower (n : ℕ) {ξ : ℝ}
    (hξ : ξ ∈ positiveBand n) :
    Real.log (frequency n) / 2 ≤ max (Real.log |ξ|) 0 := by
  have hfreq : 0 < frequency n := by linarith [frequency_ge_five n]
  have hξlower : frequency n / 2 ≤ ξ := by
    change ξ ∈ Icc (frequency n - 1) (frequency n + 1) at hξ
    linarith [hξ.1, frequency_ge_five n]
  have hξpos : 0 < ξ := lt_of_lt_of_le (by positivity) hξlower
  have hlog := Real.log_le_log (by positivity : 0 < frequency n / 2) hξlower
  rw [Real.log_div hfreq.ne' (by norm_num)] at hlog
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hL : 4 ≤ Real.log (frequency n) := by
    rw [log_frequency]
    exact frequency_exponent_ge_four n
  rw [abs_of_pos hξpos]
  exact (by linarith [hlog, hlogtwo, hL] :
    Real.log (frequency n) / 2 ≤ Real.log ξ).trans (le_max_left _ _)

private theorem spectralAmplitude_band_density_lower (n : ℕ) {ξ : ℝ}
    (hξ : ξ ∈ positiveBand n) :
    1 / (4096 * Real.pi) ≤
      max (Real.log |ξ|) 0 * spectralAmplitude ξ ^ 2 := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hA := spectralAmplitude_band_lower n hξ
  have hbase0 : 0 ≤ coeff n / (32 * s) :=
    div_nonneg (coeff_nonneg n) (by positivity)
  have hA2 : (coeff n / (32 * s)) ^ 2 ≤ spectralAmplitude ξ ^ 2 :=
    pow_le_pow_left₀ hbase0 hA 2
  have hL := positiveBand_log_lower n hξ
  have hL0 : 0 ≤ Real.log (frequency n) / 2 := by rw [log_frequency]; positivity
  have hprod := mul_le_mul hL hA2 (by positivity) (le_max_right (Real.log |ξ|) 0)
  calc
    1 / (4096 * Real.pi) =
        (Real.log (frequency n) / 2) * (coeff n / (32 * s)) ^ 2 := by
      symm
      calc
        (Real.log (frequency n) / 2) * (coeff n / (32 * s)) ^ 2 =
            (coeff n ^ 2 * Real.log (frequency n)) / (2048 * s ^ 2) := by
          field_simp [hs.ne']
          <;> ring
        _ = 1 / (4096 * Real.pi) := by
          rw [coeff_sq_log_frequency, hs2]
          congr 1
          ring
    _ ≤ max (Real.log |ξ|) 0 * spectralAmplitude ξ ^ 2 := hprod

-- This extended integral concerns the explicit amplitude computed for the
-- actual fixed source.  The source-Fourier identity remains the separate,
-- unconditional concrete obligation below; it is never an input premise.
private theorem spectralAmplitude_log_lintegral_top :
    (∫⁻ ξ : ℝ, ENNReal.ofReal
      (max (Real.log |ξ|) 0 * spectralAmplitude ξ ^ 2)) = ∞ := by
  let g : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (max (Real.log |ξ|) 0 * spectralAmplitude ξ ^ 2)
  let q : ℝ≥0∞ := ENNReal.ofReal (1 / (4096 * Real.pi))
  let κ : ℝ≥0∞ := q * 2
  have hκ : κ ≠ 0 := by
    have hpos : 0 < κ := by dsimp [κ, q]; positivity
    exact hpos.ne'
  have hvolume (n : ℕ) : volume (positiveBand n) = 2 := by
    rw [positiveBand, Real.volume_Icc]
    norm_num [show (frequency n + 1) - (frequency n - 1) = (2 : ℝ) by ring]
  have hband (n : ℕ) : κ ≤ ∫⁻ ξ in positiveBand n, g ξ := by
    calc
      κ = ∫⁻ ξ in positiveBand n, q := by
        rw [setLIntegral_const, hvolume]
      _ ≤ ∫⁻ ξ in positiveBand n, g ξ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (show MeasurableSet (positiveBand n) from
          measurableSet_Icc)] with ξ hξ
        exact ENNReal.ofReal_le_ofReal (spectralAmplitude_band_density_lower n hξ)
  have hUnion := lintegral_iUnion (μ := (volume : Measure ℝ))
    (fun n : ℕ => (show MeasurableSet (positiveBand n) from measurableSet_Icc))
    positiveBands_disjoint g
  change (∫⁻ ξ, g ξ) = ∞
  apply top_unique
  calc
    ∞ = ∑' _ : ℕ, κ := (ENNReal.tsum_const_eq_top_of_ne_zero hκ).symm
    _ ≤ ∑' n : ℕ, ∫⁻ ξ in positiveBand n, g ξ := ENNReal.tsum_le_tsum hband
    _ = ∫⁻ ξ in ⋃ n : ℕ, positiveBand n, g ξ := hUnion.symm
    _ ≤ ∫⁻ ξ, g ξ := lintegral_mono' Measure.restrict_le_self le_rfl

/- The concrete Fourier identity is

    counterProfile_unitary_fourier (ξ : ℝ) :
      unitarySourceFourier counterProfile ξ =
        sourcePhase ξ (1/2) * (spectralAmplitude ξ : ℂ).

The tent transform, cosine modulation, Haar translation, and dominated series
interchange prove this identity. Its exact norm-square formula transfers the
nonnegative spectral lintegral divergence to the actual Fourier transform.
The identity compressed_actualProfile_eq then identifies the full original
theta profile of the compressed physical source.
-/

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample


/-!
The actual tent transform is computed from interval-indicator convolution,
with the cycle-frequency Fourier convention converted to positive angular
frequency and unitary normalization.
-/

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set
open scoped Convolution FourierTransform

private def tentBox : ℝ → ℂ :=
  (Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ)).indicator (fun _ => (1 : ℂ))

private theorem tentBox_integrable : Integrable tentBox volume := by
  unfold tentBox
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact integrableOn_const (by simp [Real.volume_Icc])

private theorem tent_overlap_length (s : ℝ) :
    max (min (1 / 8 : ℝ) (s + 1 / 8) -
      max (-(1 / 8 : ℝ)) (s - 1 / 8)) 0 = max (1 / 4 - |s|) 0 := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs,
      min_eq_left (by linarith : (1 / 8 : ℝ) ≤ s + 1 / 8),
      max_eq_right (by linarith : -(1 / 8 : ℝ) ≤ s - 1 / 8)]
    congr 1 <;> ring
  · have hs' : s ≤ 0 := le_of_not_ge hs
    rw [abs_of_nonpos hs',
      min_eq_right (by linarith : s + 1 / 8 ≤ (1 / 8 : ℝ)),
      max_eq_left (by linarith : s - 1 / 8 ≤ -(1 / 8 : ℝ))]
    congr 1 <;> ring

private theorem tentBox_convolution (s : ℝ) :
    (tentBox ⋆[ContinuousLinearMap.mul ℂ ℂ] tentBox) s =
      ((max (1 / 4 - |s|) 0 : ℝ) : ℂ) := by
  rw [MeasureTheory.convolution_mul]
  have hprod : (fun t : ℝ => tentBox t * tentBox (s - t)) =
      (Icc (max (-(1 / 8 : ℝ)) (s - 1 / 8))
        (min (1 / 8 : ℝ) (s + 1 / 8))).indicator (fun _ => (1 : ℂ)) := by
    funext t
    have hmem : t ∈ Icc (max (-(1 / 8 : ℝ)) (s - 1 / 8))
          (min (1 / 8 : ℝ) (s + 1 / 8)) ↔
        t ∈ Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∧
          s - t ∈ Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ) := by
      simp only [mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
        exact ⟨⟨h₁, h₃⟩, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
        exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩
    by_cases ht : t ∈ Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ)
    · by_cases hu : s - t ∈ Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ)
      · have ho := hmem.mpr ⟨ht, hu⟩
        simp only [tentBox, Set.indicator_of_mem ht, Set.indicator_of_mem hu,
          Set.indicator_of_mem ho, mul_one]
      · have ho : t ∉ Icc (max (-(1 / 8 : ℝ)) (s - 1 / 8))
            (min (1 / 8 : ℝ) (s + 1 / 8)) := fun h => hu (hmem.mp h).2
        simp only [tentBox, Set.indicator_of_notMem hu,
          Set.indicator_of_notMem ho, mul_zero]
    · have ho : t ∉ Icc (max (-(1 / 8 : ℝ)) (s - 1 / 8))
          (min (1 / 8 : ℝ) (s + 1 / 8)) := fun h => ht (hmem.mp h).1
      simp only [tentBox, Set.indicator_of_notMem ht,
        Set.indicator_of_notMem ho, zero_mul]
  rw [hprod, integral_indicator_const (1 : ℂ) measurableSet_Icc,
    Real.volume_real_Icc, Complex.real_smul, mul_one, tent_overlap_length]

private theorem tent_four_overlap (s : ℝ) :
    4 * max (1 / 4 - |s|) 0 = tent s := by
  unfold tent
  by_cases hs : 0 ≤ 1 / 4 - |s|
  · rw [max_eq_left hs, max_eq_left (by linarith : 0 ≤ 1 - 4 * |s|)]
    ring
  · rw [max_eq_right (le_of_not_ge hs),
      max_eq_right (by linarith : 1 - 4 * |s| ≤ 0)]
    ring

private theorem tent_eq_four_convolution :
    (fun s : ℝ => (tent s : ℂ)) =
      fun s => (4 : ℂ) * (tentBox ⋆[ContinuousLinearMap.mul ℂ ℂ] tentBox) s := by
  funext s
  rw [tentBox_convolution]
  calc
    (tent s : ℂ) = ((4 * max (1 / 4 - |s|) 0 : ℝ) : ℂ) :=
      congrArg Complex.ofReal (tent_four_overlap s).symm
    _ = (4 : ℂ) * ((max (1 / 4 - |s|) 0 : ℝ) : ℂ) := by push_cast; ring

-- This exact integral includes ξ = 0 and both signs of ξ.
private theorem tentBox_interval_fourier (ξ : ℝ) :
    (∫ t in (-(1 / 8 : ℝ))..(1 / 8 : ℝ),
      Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)) =
      (((1 / 4 : ℝ) * Real.sinc (ξ / 8) : ℝ) : ℂ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    norm_num [intervalIntegral.integral_const]
  have h := intervalIntegral.integral_comp_mul_left
    (a := -(1 / 8 : ℝ)) (b := (1 / 8 : ℝ)) (c := ξ)
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hξ
  rw [show ξ * (-(1 / 8 : ℝ)) = -(ξ / 8) by ring,
    show ξ * (1 / 8 : ℝ) = ξ / 8 by ring,
    integral_exp_mul_I_eq_sinc] at h
  rw [h, Complex.real_smul]
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
  push_cast
  field_simp [hξ, hξc] <;> ring

private theorem tentBox_raw_fourier_plus (ξ : ℝ) :
    𝓕 tentBox (-ξ / (2 * Real.pi)) =
      (((1 / 4 : ℝ) * Real.sinc (ξ / 8) : ℝ) : ℂ) := by
  have hscale (t : ℝ) :
      -2 * Real.pi * inner ℝ t (-ξ / (2 * Real.pi)) = ξ * t := by
    simp only [Real.inner_apply]
    field_simp [Real.pi_ne_zero] <;> ring
  calc
    𝓕 tentBox (-ξ / (2 * Real.pi)) =
        ∫ t : ℝ, (Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ)).indicator
          (fun t => Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)) t := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with t
      rw [hscale]
      by_cases ht : t ∈ Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ)
      · simp only [tentBox, smul_eq_mul, Set.indicator_of_mem ht,
          mul_one]
      · simp only [tentBox, smul_eq_mul, Set.indicator_of_notMem ht,
          mul_zero]
    _ = ∫ t : ℝ in Icc (-(1 / 8 : ℝ)) (1 / 8 : ℝ),
        Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I) := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ t in (-(1 / 8 : ℝ))..(1 / 8 : ℝ),
        Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : -(1 / 8 : ℝ) ≤ 1 / 8)]
    _ = (((1 / 4 : ℝ) * Real.sinc (ξ / 8) : ℝ) : ℂ) :=
      tentBox_interval_fourier ξ

private theorem tent_raw_fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (θ : ℝ) :
    𝓕 (fun t => c * f t) θ = c * 𝓕 f θ := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  ring

private theorem tent_raw_fourier_plus (ξ : ℝ) :
    𝓕 (fun t : ℝ => (tent t : ℂ)) (-ξ / (2 * Real.pi)) =
      (((1 / 4 : ℝ) * Real.sinc (ξ / 8) ^ 2 : ℝ) : ℂ) := by
  rw [tent_eq_four_convolution, tent_raw_fourier_const_mul,
    Real.fourier_mul_convolution_eq tentBox_integrable tentBox_integrable,
    tentBox_raw_fourier_plus]
  push_cast
  ring

/-- The actual paper-unitary plus Fourier transform of the concrete tent.
No Fourier formula is supplied as a premise. This includes ξ = 0. -/
private theorem tent_unitary_fourier (ξ : ℝ) :
    unitarySourceFourier (fun t => (tent t : ℂ)) ξ = (tentSourceHat ξ : ℂ) := by
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne'
  have hsc : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold unitarySourceFourier tentSourceHat
  rw [tent_raw_fourier_plus]
  push_cast
  field_simp [hsc] <;> ring

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample


/- The spatial-series Fourier interchange is justified by an integrable
coefficient-times-tent majorant. The Fourier formula and its divergence are
proved for the explicit source. -/

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set
open scoped FourierTransform

private def sourcePhase (ξ t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))

private def spatialTerm (n : ℕ) (t : ℝ) : ℂ :=
  ((coeff n * tent (t - 1 / 2) *
    Real.cos (frequency n * (t - 1 / 2)) : ℝ) : ℂ)

private theorem sourcePhase_norm (ξ t : ℝ) : ‖sourcePhase ξ t‖ = 1 := by
  simp [sourcePhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem tent_hasCompactSupport : HasCompactSupport tent := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -(1 / 4 : ℝ)) (b := 1 / 4))
  intro t ht
  change tent t ≠ 0 at ht
  by_contra hnot
  have habs : (1 / 4 : ℝ) ≤ |t| := by
    apply le_of_not_gt
    intro hsmall
    have hsmall' := abs_lt.mp hsmall
    exact hnot ⟨by linarith [hsmall'.1], by linarith [hsmall'.2]⟩
  exact ht (tent_zero_of_quarter_le habs)

private theorem unitarySourceFourier_eq_integral (u : ℝ → ℂ) (ξ : ℝ) :
    unitarySourceFourier u ξ =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, sourcePhase ξ t * u t := by
  rw [unitarySourceFourier, ← Zeta23.paperFT_ofReal_eq_fourier u ξ]
  congr 1
  unfold Zeta23.paperFT
  apply integral_congr_ae
  filter_upwards with t
  dsimp [sourcePhase]
  ring

private theorem actual_spatial_series_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => spatialTerm n t) (counterProfile t) := by
  have hs : HasSum
      (fun n : ℕ => coeff n * Real.cos (frequency n * (t - 1 / 2)))
      (carrierSeries t) :=
    (coeff_hasSum.summable.of_norm_bounded fun n => carrierTerm_norm_le n t).hasSum
  have hc : HasSum
      (fun n : ℕ => ((coeff n * Real.cos (frequency n * (t - 1 / 2)) : ℝ) : ℂ))
      ((carrierSeries t : ℝ) : ℂ) := Complex.ofRealCLM.hasSum hs
  have hm := hc.mul_left ((tent (t - 1 / 2) : ℝ) : ℂ)
  convert hm using 1
  · funext n
    dsimp [spatialTerm]
    push_cast
    ring
  · dsimp [counterProfile, counterProfileReal]
    push_cast
    ring

private theorem actual_kernel_term_norm_bound (ξ t : ℝ) (n : ℕ) :
    ‖sourcePhase ξ t * spatialTerm n t‖ ≤ coeff n * tent (t - 1 / 2) := by
  rw [norm_mul, sourcePhase_norm, one_mul]
  dsimp [spatialTerm]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (coeff_nonneg n), abs_of_nonneg (tent_nonneg _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_cos_le_one (frequency n * (t - 1 / 2)))
    (mul_nonneg (coeff_nonneg n) (tent_nonneg (t - 1 / 2)))

-- The exact coefficient/tent majorant integrates to a finite number before
-- interchanging the infinite real/complex series and Fourier integral.
private theorem actual_counterProfile_fourier_hasSum (ξ : ℝ) :
    HasSum (fun n : ℕ => unitarySourceFourier (spatialTerm n) ξ)
      (unitarySourceFourier counterProfile ξ) := by
  have htent : Integrable tent :=
    tent_continuous.integrable_of_hasCompactSupport tent_hasCompactSupport
  have hshift : Integrable (fun t : ℝ => tent (t - 1 / 2)) := by
    simpa only [sub_eq_add_neg] using htent.comp_add_right (-(1 / 2 : ℝ))
  have hbound : Integrable
      (fun t : ℝ => ∑' n : ℕ, coeff n * tent (t - 1 / 2)) := by
    simpa only [tsum_mul_right, coeff_hasSum.tsum_eq, one_mul] using hshift
  have hsum := hasSum_integral_of_dominated_convergence
    (fun (n : ℕ) (t : ℝ) => coeff n * tent (t - 1 / 2))
    (F := fun (n : ℕ) (t : ℝ) => sourcePhase ξ t * spatialTerm n t)
    (f := fun t : ℝ => sourcePhase ξ t * counterProfile t)
    (fun n => (show Continuous (fun t : ℝ =>
      sourcePhase ξ t * spatialTerm n t) from by
        dsimp [sourcePhase, spatialTerm, tent]
        fun_prop).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t => actual_kernel_term_norm_bound ξ t n)
    (Filter.Eventually.of_forall fun t =>
      coeff_hasSum.summable.mul_right (tent (t - 1 / 2)))
    hbound
    (Filter.Eventually.of_forall fun t =>
      (actual_spatial_series_hasSum t).mul_left (sourcePhase ξ t))
  have hscaled := hsum.mul_left (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹)
  simpa only [unitarySourceFourier_eq_integral] using hscaled

private theorem sourcePhase_add_time (ξ s t : ℝ) :
    sourcePhase ξ (s + t) = sourcePhase ξ s * sourcePhase ξ t := by
  unfold sourcePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem sourcePhase_add_frequency (ξ η t : ℝ) :
    sourcePhase (ξ + η) t = sourcePhase ξ t * sourcePhase η t := by
  unfold sourcePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem actual_cos_eq_two_phases (η t : ℝ) :
    (Real.cos (η * t) : ℂ) =
      (sourcePhase η t + sourcePhase (-η) t) / 2 := by
  rw [Complex.ofReal_cos]
  unfold Complex.cos sourcePhase
  congr 1
  congr 1 <;> congr 1 <;> push_cast <;> ring

-- Translation is obtained from actual Haar translation of the integral.
-- It does not assume any Fourier formula for the profile.
private theorem unitarySourceFourier_translate (u : ℝ → ℂ) (a ξ : ℝ) :
    unitarySourceFourier (fun t => u (t - a)) ξ =
      sourcePhase ξ a * unitarySourceFourier u ξ := by
  rw [unitarySourceFourier_eq_integral, unitarySourceFourier_eq_integral]
  have hshift : (∫ t : ℝ, sourcePhase ξ t * u (t - a)) =
      ∫ t : ℝ, sourcePhase ξ (t + a) * u t := by
    simpa only [add_sub_cancel_right] using
      (integral_add_right_eq_self (fun t : ℝ => sourcePhase ξ t * u (t - a)) a).symm
  have hpoint : (fun t : ℝ => sourcePhase ξ (t + a) * u t) =
      fun t => sourcePhase ξ a * (sourcePhase ξ t * u t) := by
    funext t
    rw [sourcePhase_add_time]
    ring
  rw [hshift, hpoint, integral_const_mul]
  ring

private theorem actual_tent_kernel_integrable (η : ℝ) :
    Integrable (fun t : ℝ => sourcePhase η t * (tent t : ℂ)) := by
  have ht : Integrable (fun t : ℝ => (tent t : ℂ)) :=
    Complex.ofRealCLM.integrable_comp
      (tent_continuous.integrable_of_hasCompactSupport tent_hasCompactSupport)
  exact ht.bdd_mul
    (show AEStronglyMeasurable (fun t : ℝ => sourcePhase η t) volume from by
      apply Continuous.aestronglyMeasurable
      unfold sourcePhase
      fun_prop)
    (Filter.Eventually.of_forall fun t => (sourcePhase_norm η t).le)

private def centeredSpatialTerm (n : ℕ) (t : ℝ) : ℂ :=
  ((coeff n * tent t * Real.cos (frequency n * t) : ℝ) : ℂ)

private theorem actual_single_kernel_identity (n : ℕ) (ξ t : ℝ) :
    sourcePhase ξ t * centeredSpatialTerm n t =
      ((coeff n / 2 : ℝ) : ℂ) *
        (sourcePhase (ξ - frequency n) t * (tent t : ℂ) +
          sourcePhase (ξ + frequency n) t * (tent t : ℂ)) := by
  simp only [centeredSpatialTerm, Complex.ofReal_mul]
  rw [actual_cos_eq_two_phases,
    show ξ - frequency n = ξ + (-frequency n) by ring,
    sourcePhase_add_frequency, sourcePhase_add_frequency]
  push_cast
  ring

-- The tent identity used below follows from the interval-indicator
-- convolution proof above and has the exact unitary normalization.
-- Both modulation channels are retained in the spectral amplitude.
private theorem actual_centered_term_fourier (n : ℕ) (ξ : ℝ) :
    unitarySourceFourier (centeredSpatialTerm n) ξ = (spectralTerm n ξ : ℂ) := by
  rw [unitarySourceFourier_eq_integral]
  simp_rw [actual_single_kernel_identity]
  rw [integral_const_mul,
    integral_add (actual_tent_kernel_integrable (ξ - frequency n))
      (actual_tent_kernel_integrable (ξ + frequency n))]
  calc
    _ = ((coeff n / 2 : ℝ) : ℂ) *
        (unitarySourceFourier (fun t : ℝ => (tent t : ℂ)) (ξ - frequency n) +
          unitarySourceFourier (fun t : ℝ => (tent t : ℂ)) (ξ + frequency n)) := by
      rw [unitarySourceFourier_eq_integral, unitarySourceFourier_eq_integral]
      ring
    _ = (spectralTerm n ξ : ℂ) := by
      rw [tent_unitary_fourier, tent_unitary_fourier]
      unfold spectralTerm
      push_cast
      ring

private theorem actual_spatial_term_fourier (n : ℕ) (ξ : ℝ) :
    unitarySourceFourier (spatialTerm n) ξ =
      sourcePhase ξ (1 / 2) * (spectralTerm n ξ : ℂ) := by
  have hterm : spatialTerm n = fun t : ℝ => centeredSpatialTerm n (t - 1 / 2) := rfl
  rw [hterm, unitarySourceFourier_translate, actual_centered_term_fourier]

private theorem counterProfile_unitary_fourier (ξ : ℝ) :
    unitarySourceFourier counterProfile ξ =
      sourcePhase ξ (1 / 2) * (spectralAmplitude ξ : ℂ) := by
  have hs : HasSum (fun n : ℕ => (spectralTerm n ξ : ℂ))
      (spectralAmplitude ξ : ℂ) :=
    Complex.ofRealCLM.hasSum (spectralTerm_summable ξ).hasSum
  have hs' := hs.mul_left (sourcePhase ξ (1 / 2))
  have ht := actual_counterProfile_fourier_hasSum ξ
  simp_rw [actual_spatial_term_fourier] at ht
  exact ht.unique hs'

private theorem actual_counterProfile_fourier_norm_sq (ξ : ℝ) :
    ‖unitarySourceFourier counterProfile ξ‖ ^ 2 = spectralAmplitude ξ ^ 2 := by
  rw [counterProfile_unitary_fourier, norm_mul, sourcePhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

-- Actual fixed source, actual raw unitary Fourier transform, genuinely
-- extended-valued positive-log integral.  No totalized integral criterion.
private theorem actual_counterProfile_positive_log_top :
    (∫⁻ ξ : ℝ, ENNReal.ofReal
      (max (Real.log |ξ|) 0 * ‖unitarySourceFourier counterProfile ξ‖ ^ 2)) = ∞ := by
  simp_rw [actual_counterProfile_fourier_norm_sq]
  exact spectralAmplitude_log_lintegral_top

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol

private def gammaRatio (ξ : ℝ) : ℝ :=
  (ξ ^ 2 + 1 / 16) / (ξ ^ 2 + 25 / 16)

private def gammaDensity (ξ : ℝ) : ℝ :=
  (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ) +
    Complex.I * (ξ : ℂ))).re - Real.log Real.pi

def gammaWeight (ξ : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * (gammaRatio ξ * gammaDensity ξ) +
    1 + 4 * Real.sqrt Real.pi

private def domainConstant : ℝ :=
  2 * Real.sqrt Real.pi + 4 * (|Real.log Real.pi| + 5)

-- The literal reference Gamma weight is strictly larger than one, and
-- it dominates the positive logarithmic frequency weight up to a finite constant.
private theorem actualGammaWeight_bounds (ξ : ℝ) :
    1 < gammaWeight ξ ∧
      max (Real.log |ξ|) 0 ≤ domainConstant * gammaWeight ξ := by
  let s : ℝ := Real.sqrt Real.pi
  let a : ℝ := 2 / s
  let B : ℝ := |Real.log Real.pi| + 5
  have hs : 0 < s := Real.sqrt_pos.2 Real.pi_pos
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < ξ ^ 2 + 25 / 16 := by positivity
  have hR0 : 0 ≤ gammaRatio ξ := by dsimp [gammaRatio]; positivity
  have hR1 : gammaRatio ξ ≤ 1 := by
    dsimp [gammaRatio]
    exact (div_le_one hden).2 (by linarith)
  have hdMu : gammaDensity ξ = 2 * Real.pi * Zeta23.mu (2 * ξ) := by
    have harg : (1 / 4 : ℂ) + Complex.I * ((2 * ξ : ℝ) : ℂ) / 2 =
        ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * (ξ : ℂ)) := by
      push_cast
      ring
    dsimp [gammaDensity, Zeta23.mu]
    rw [harg]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hd : -(2 * Real.pi) < gammaDensity ξ := by
    have hmu : (-1 : ℝ) < Zeta23.mu (2 * ξ) :=
      Zeta23.MuFields.neg_one_lt_mu_zero.trans_le
        (Zeta23.MuFields.mu_zero_le (2 * ξ))
    have hmul := mul_lt_mul_of_pos_left hmu
      (show 0 < 2 * Real.pi by positivity)
    rw [hdMu]
    simpa using hmul
  have hRd : -(2 * Real.pi) < gammaRatio ξ * gammaDensity ξ := by
    by_cases hd0 : 0 ≤ gammaDensity ξ
    · exact lt_of_lt_of_le (by linarith [Real.pi_pos]) (mul_nonneg hR0 hd0)
    · have hd0' : gammaDensity ξ ≤ 0 := le_of_not_ge hd0
      have hmul := mul_le_mul_of_nonpos_right hR1 hd0'
      exact hd.trans_le (by simpa using hmul)
  have hscale : a * (2 * Real.pi) = 4 * s := by
    dsimp [a, s]
    field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']
    <;> nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hp : 1 < gammaWeight ξ := by
    have hmul := mul_lt_mul_of_pos_left hRd ha
    change 1 < a * (gammaRatio ξ * gammaDensity ξ) + 1 + 4 * s
    nlinarith [hmul, hscale]
  refine ⟨hp, ?_⟩
  by_cases hsmall : |ξ| ≤ 1
  · have hlog : Real.log |ξ| ≤ 0 := Real.log_nonpos (abs_nonneg ξ) hsmall
    rw [max_eq_right hlog]
    exact mul_nonneg (by dsimp [domainConstant]; positivity) (by linarith [hp])
  · have hr : 1 < |ξ| := lt_of_not_ge hsmall
    have hsq : 1 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
    have hsq0 : 0 < ξ ^ 2 := by linarith
    have hRquarter : (1 / 4 : ℝ) ≤ gammaRatio ξ := by
      dsimp [gammaRatio]
      apply (le_div_iff₀ hden).2
      nlinarith [hsq]
    have hst := Zeta23.StirlingVert.re_digamma_stirling'
      (a := 1 / 4) (t := ξ) (by norm_num) (by norm_num) (by linarith [hr])
    have herr : 5 / ξ ^ 2 ≤ 5 :=
      (div_le_iff₀ hsq0).2 (by nlinarith [hsq])
    have hdlo : Real.log |ξ| - B ≤ gammaDensity ξ := by
      have hstlo := (abs_le.mp hst).1
      dsimp [gammaDensity, B]
      linarith [hstlo, herr, le_abs_self (Real.log Real.pi)]
    have hlog0 : 0 ≤ Real.log |ξ| := Real.log_nonneg hr.le
    have hRL := mul_le_mul_of_nonneg_right hRquarter hlog0
    have hRB := mul_le_mul_of_nonneg_right hR1 hB
    have hRD := mul_le_mul_of_nonneg_left hdlo hR0
    have hlow : Real.log |ξ| / 4 - B ≤ gammaRatio ξ * gammaDensity ξ := by
      nlinarith [hRL, hRB, hRD]
    have hpmain : a * (Real.log |ξ| / 4 - B) ≤ gammaWeight ξ := by
      have hmul := mul_le_mul_of_nonneg_left hlow ha.le
      change a * (Real.log |ξ| / 4 - B) ≤
        a * (gammaRatio ξ * gammaDensity ξ) + 1 + 4 * s
      linarith [hmul, hs]
    have hdiv : Real.log |ξ| ≤
        (4 * (gammaWeight ξ + a * B)) / a := by
      apply (le_div_iff₀ ha).2
      nlinarith [hpmain]
    have hfour : 4 / a = 2 * s := by
      dsimp [a]
      field_simp [hs.ne']
      <;> ring
    have hL : Real.log |ξ| ≤ 2 * s * gammaWeight ξ + 4 * B := by
      calc
        Real.log |ξ| ≤ (4 * (gammaWeight ξ + a * B)) / a := hdiv
        _ = (4 / a) * gammaWeight ξ + 4 * B := by
          field_simp [ha.ne']
          <;> ring
        _ = 2 * s * gammaWeight ξ + 4 * B := by rw [hfour]
    have hBscale : 4 * B ≤ 4 * B * gammaWeight ξ :=
      le_mul_of_one_le_right (by positivity) (by linarith [hp])
    rw [max_eq_left hlog0]
    change Real.log |ξ| ≤ (2 * s + 4 * B) * gammaWeight ξ
    nlinarith [hL, hBscale]

-- Every constant shift admitted by the literal lower bound remains large
-- enough to dominate log-plus. The constant may depend on that shift.
private theorem actualGammaWeight_shifted_log_bound (c : ℝ)
    (hc : ∀ ξ : ℝ, 1 ≤ gammaWeight ξ + c) (ξ : ℝ) :
    max (Real.log |ξ|) 0 ≤
      (domainConstant * (1 + |c|)) * (gammaWeight ξ + c) := by
  have hC : 0 ≤ domainConstant := by
    unfold domainConstant
    positivity
  have hscale : |c| ≤ |c| * (gammaWeight ξ + c) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hc ξ) (abs_nonneg c)
  have hp : gammaWeight ξ ≤ (1 + |c|) * (gammaWeight ξ + c) := by
    calc
      gammaWeight ξ ≤ (gammaWeight ξ + c) + |c| := by
        linarith [neg_le_abs c]
      _ ≤ (gammaWeight ξ + c) + |c| * (gammaWeight ξ + c) :=
        by linarith [hscale]
      _ = (1 + |c|) * (gammaWeight ξ + c) := by ring
  calc
    max (Real.log |ξ|) 0 ≤ domainConstant * gammaWeight ξ :=
      (actualGammaWeight_bounds ξ).2
    _ ≤ domainConstant * ((1 + |c|) * (gammaWeight ξ + c)) :=
      mul_le_mul_of_nonneg_left hp hC
    _ = (domainConstant * (1 + |c|)) * (gammaWeight ξ + c) := by ring

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol


/- The literal symbol comparison and explicit profile feed the compressed
physical witness, with full theta and the actual positive-log divergence. -/

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set
open scoped ENNReal

/-- The original physical Hilbert space and sixth moment, without a
coefficient-space or truncated-theta reinterpretation. -/
def originalPhysicalH6 (F : ℝ → ℂ) : Prop :=
  MemLp F 2 (volume.restrict (Ioi Real.pi)) ∧
    Integrable (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2)
      (volume.restrict (Ioi Real.pi))

/-- Literal actual Gamma form with relative constant shift c, on a source
whose actual profile is L1 as proved for the explicit counterexample.
Admissibility means gammaWeight+c >= 1 everywhere in the theorem below.
Integrable is genuine finite energy, not a totalized integral criterion. -/
def originalGammaFormDomain (c : ℝ) (F : ℝ → ℂ) : Prop :=
  Integrable (fun ξ : ℝ =>
    (Symbol.gammaWeight ξ + c) *
      ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2) volume

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample


/- Compression preserves the positive-log Fourier divergence while the
logarithmic support enforces any original sixth-moment ratio cap K>1.
The witness is the same source for all admissible Gamma shifts. -/
namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology

private def compressedProfile (κ t : ℝ) : ℂ := counterProfile (t / κ)
private def compressedFeature (κ : ℝ) : ℝ → ℂ := sourceOfProfile (compressedProfile κ)

private theorem compressed_zero (κ : ℝ) : compressedProfile κ 0 = 0 := by
  have hz : counterProfile 0 = 0 := profile_zero_off (by norm_num)
  simpa [compressedProfile] using hz

private theorem compressed_continuous (κ : ℝ) : Continuous (compressedProfile κ) :=
  profile_continuous.comp (continuous_id.div_const κ)

private theorem compressed_zero_off {κ : ℝ} (hκ : 0 < κ) {t : ℝ}
    (ht : t ∉ Icc (κ / 4) (3 * κ / 4)) : compressedProfile κ t = 0 := by
  apply profile_zero_off
  intro h
  apply ht
  have ha := (le_div_iff₀ hκ).mp h.1
  have hb := (div_le_iff₀ hκ).mp h.2
  constructor <;> nlinarith [ha, hb]

private theorem compressed_compact {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (compressedProfile κ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
  intro t ht
  by_contra h
  exact ht (compressed_zero_off hκ h)

private theorem compressed_center {κ : ℝ} (hκ : 0 < κ) :
    compressedProfile κ (κ / 2) = 1 := by
  have he : κ / 2 / κ = (1 / 2 : ℝ) := by field_simp [hκ.ne']
  simpa [compressedProfile, he] using profile_center

private theorem compressed_L1 {κ : ℝ} (hκ : 0 < κ) :
    Integrable (compressedProfile κ) volume :=
  (compressed_continuous κ).integrable_of_hasCompactSupport (compressed_compact hκ)

private theorem compressed_profile_memLp {κ : ℝ} (hκ : 0 < κ) :
    MemLp (compressedProfile κ) 2 volume :=
  (compressed_continuous κ).memLp_of_hasCompactSupport (compressed_compact hκ)

private theorem compressed_fourier {κ : ℝ} (hκ : 0 < κ) (ξ : ℝ) :
    unitarySourceFourier (compressedProfile κ) ξ =
      (κ : ℂ) * unitarySourceFourier counterProfile (κ * ξ) := by
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hp (t : ℝ) : sourcePhase ξ t = sourcePhase (κ * ξ) (t / κ) := by
    unfold sourcePhase
    congr 1
    push_cast
    field_simp [hκc] <;> ring
  have hi : (∫ t : ℝ, sourcePhase ξ t * compressedProfile κ t) =
      κ • ∫ t : ℝ, sourcePhase (κ * ξ) t * counterProfile t := by
    calc
      _ = ∫ t : ℝ, sourcePhase (κ * ξ) (t / κ) * counterProfile (t / κ) := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [compressedProfile, hp]
      _ = κ • ∫ t : ℝ, sourcePhase (κ * ξ) t * counterProfile t := by
        simpa only [abs_of_pos hκ] using
          Measure.integral_comp_div
            (fun t : ℝ => sourcePhase (κ * ξ) t * counterProfile t) κ
  rw [unitarySourceFourier_eq_integral, unitarySourceFourier_eq_integral, hi,
    Complex.real_smul]
  ring

private theorem compressed_fourier_norm_sq {κ : ℝ} (hκ : 0 < κ) (ξ : ℝ) :
    ‖unitarySourceFourier (compressedProfile κ) ξ‖ ^ 2 =
      κ ^ 2 * ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2 := by
  rw [compressed_fourier hκ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hκ, mul_pow]

private theorem compressed_logplus_comparison {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ξ : ℝ) :
    max (Real.log |κ * ξ|) 0 ≤ max (Real.log |ξ|) 0 := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  have ha : 0 < |κ * ξ| := abs_pos.mpr (mul_ne_zero hκ.ne' hξ)
  have hb : |κ * ξ| ≤ |ξ| := by
    rw [abs_mul, abs_of_pos hκ]
    exact mul_le_of_le_one_left (abs_nonneg ξ) hκ1
  exact max_le_max (Real.log_le_log ha hb) le_rfl

private theorem compressed_positive_log_top {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
      ‖unitarySourceFourier (compressedProfile κ) ξ‖ ^ 2)) = ∞ := by
  let g : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (max (Real.log |ξ|) 0 * ‖unitarySourceFourier counterProfile ξ‖ ^ 2)
  have he : MeasurableEmbedding (fun ξ : ℝ => κ * ξ) :=
    (Homeomorph.mulLeft₀ κ hκ.ne').isClosedEmbedding.measurableEmbedding
  have hc : (∫⁻ ξ : ℝ, g (κ * ξ)) =
      ENNReal.ofReal |κ⁻¹| * ∫⁻ ξ : ℝ, g ξ := by
    rw [← he.lintegral_map g, Real.map_volume_mul_left hκ.ne', lintegral_smul_measure, smul_eq_mul]
  have hn : ENNReal.ofReal |κ⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hκ.ne'))).ne'
  have hs : (∫⁻ ξ : ℝ, g (κ * ξ)) = ∞ := by
    rw [hc]
    have hg : (∫⁻ ξ : ℝ, g ξ) = ∞ := actual_counterProfile_positive_log_top
    rw [hg]
    exact ENNReal.mul_top hn
  have hκ2 : ENNReal.ofReal (κ ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hκ)).ne'
  apply top_unique
  calc
    ∞ = ENNReal.ofReal (κ ^ 2) * ∫⁻ ξ : ℝ, g (κ * ξ) := by simp [hs, hκ2]
    _ = ∫⁻ ξ : ℝ, ENNReal.ofReal (κ ^ 2) * g (κ * ξ) :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
        ‖unitarySourceFourier (compressedProfile κ) ξ‖ ^ 2) := by
      apply lintegral_mono
      intro ξ
      dsimp [g]
      rw [← ENNReal.ofReal_mul (sq_nonneg κ)]
      apply ENNReal.ofReal_le_ofReal
      rw [compressed_fourier_norm_sq hκ]
      calc
        κ ^ 2 * (max (Real.log |κ * ξ|) 0 *
            ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2) =
            max (Real.log |κ * ξ|) 0 *
              (κ ^ 2 * ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2) := by ring
        _ ≤ max (Real.log |ξ|) 0 *
            (κ ^ 2 * ‖unitarySourceFourier counterProfile (κ * ξ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (compressed_logplus_comparison hκ hκ1 ξ)
            (by positivity)

private theorem compressedFeature_support {κ : ℝ} (hκ : 0 < κ) :
    Function.support (compressedFeature κ) ⊆
      Icc Real.pi (Real.pi * Real.exp (3 * κ / 4)) := by
  intro x hx
  have hπ : Real.pi ≤ x := by
    by_contra h
    exact hx (by simp [compressedFeature, sourceOfProfile, h])
  refine ⟨hπ, ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le Real.pi_pos hπ
  have hprof : compressedProfile κ (Real.log (x / Real.pi)) ≠ 0 := by
    intro hz
    exact hx (by simp [compressedFeature, sourceOfProfile, hπ, hz])
  have ht : Real.log (x / Real.pi) ∈ Icc (κ / 4) (3 * κ / 4) := by
    by_contra h
    exact hprof (compressed_zero_off hκ h)
  have he := Real.exp_le_exp.mpr ht.2
  rw [Real.exp_log (div_pos hxpos Real.pi_pos)] at he
  simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).mp he

private theorem compressedFeature_compact {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (compressedFeature κ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (compressedFeature_support hκ)

-- Clamp x at pi only for the continuity proof; the literal source definition
-- and all physical/full-theta identities remain unchanged.
private theorem compressedFeature_continuous {κ : ℝ} (hκ : 0 < κ) :
    Continuous (compressedFeature κ) := by
  have he : compressedFeature κ = fun x : ℝ =>
      (((max Real.pi x) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) *
        compressedProfile κ (Real.log (max Real.pi x / Real.pi)) := by
    funext x
    by_cases hx : Real.pi ≤ x
    · simp [compressedFeature, sourceOfProfile, hx, max_eq_right hx]
    · simp [compressedFeature, sourceOfProfile, hx,
        max_eq_left (le_of_not_ge hx), Real.pi_ne_zero, compressed_zero]
  rw [he]
  have hm : Continuous (fun x : ℝ => max Real.pi x) := continuous_const.max continuous_id
  have hn (x : ℝ) : max Real.pi x ≠ 0 :=
    (lt_of_lt_of_le Real.pi_pos (le_max_left _ _)).ne'
  have hr := hm.rpow_const (p := (-9 / 4 : ℝ)) (fun x => Or.inl (hn x))
  have hl : Continuous (fun x : ℝ => Real.log (max Real.pi x / Real.pi)) :=
    (hm.div_const Real.pi).log (fun x => div_ne_zero (hn x) Real.pi_ne_zero)
  exact (Complex.continuous_ofReal.comp hr).mul ((compressed_continuous κ).comp hl)

private theorem compressedFeature_zero_le_pi {κ : ℝ} (hκ : 0 < κ)
    {x : ℝ} (hx : x ≤ Real.pi) : compressedFeature κ x = 0 := by
  by_cases he : x = Real.pi
  · subst x
    simp [compressedFeature, sourceOfProfile, Real.pi_ne_zero, compressed_zero]
  · have hn : ¬ Real.pi ≤ x := fun h => he (le_antisymm hx h)
    simp [compressedFeature, sourceOfProfile, hn]

private theorem compressedFeature_real (κ x : ℝ) : (compressedFeature κ x).im = 0 := by
  by_cases hx : Real.pi ≤ x <;>
    simp [compressedFeature, sourceOfProfile, hx, compressedProfile,
      counterProfile, Complex.mul_im]

private theorem compressedFeature_center_ne {κ : ℝ} (hκ : 0 < κ) :
    compressedFeature κ (Real.pi * Real.exp (κ / 2)) ≠ 0 := by
  have hx : Real.pi ≤ Real.pi * Real.exp (κ / 2) := by
    have he := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ κ / 2)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hl : Real.log ((Real.pi * Real.exp (κ / 2)) / Real.pi) = κ / 2 := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
  have hn : (Real.pi * Real.exp (κ / 2)) ^ (-9 / 4 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (mul_pos Real.pi_pos (Real.exp_pos _)) _).ne'
  have hnc : (((Real.pi * Real.exp (κ / 2)) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast hn
  simpa [compressedFeature, sourceOfProfile, hx, hl, compressed_center hκ] using hnc

private theorem compressed_density_compact {κ : ℝ} (hκ : 0 < κ) (w : ℝ → ℝ) :
    HasCompactSupport (fun x : ℝ => w x * ‖compressedFeature κ x‖ ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.pi) (b := Real.pi * Real.exp (3 * κ / 4)))
  intro x hx
  by_contra h
  have hz : compressedFeature κ x = 0 := by
    by_contra hn
    exact h (compressedFeature_support hκ hn)
  exact hx (by simp [hz])

private theorem compressed_mass_integrable {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : ℝ => ‖compressedFeature κ x‖ ^ 2) volume := by
  have hc : Continuous (fun x : ℝ => ‖compressedFeature κ x‖ ^ (2 : ℕ)) :=
    (compressedFeature_continuous hκ).norm.pow 2
  have hs := compressed_density_compact hκ (fun _ : ℝ => 1)
  exact hc.integrable_of_hasCompactSupport (by simpa only [one_mul] using hs)

private theorem compressed_sixth_integrable {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
      ‖compressedFeature κ x‖ ^ 2) volume := by
  have hc : Continuous (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
      ‖compressedFeature κ x‖ ^ 2) :=
    ((continuous_id.div_const Real.pi).pow 6).mul
      ((compressedFeature_continuous hκ).norm.pow 2)
  exact hc.integrable_of_hasCompactSupport
    (compressed_density_compact hκ (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ)))

private theorem compressed_original_h6 {κ : ℝ} (hκ : 0 < κ) :
    originalPhysicalH6 (compressedFeature κ) := by
  refine ⟨?_, (compressed_sixth_integrable hκ).integrableOn⟩
  exact ((compressedFeature_continuous hκ).memLp_of_hasCompactSupport
    (compressedFeature_compact hκ)).mono_measure Measure.restrict_le_self

private theorem compressed_mass_Ioi_eq {κ : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in Ioi Real.pi, ‖compressedFeature κ x‖ ^ 2) =
      ∫ x : ℝ, ‖compressedFeature κ x‖ ^ 2 := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioi Real.pi
  · simp [hx]
  · have hz := compressedFeature_zero_le_pi hκ (le_of_not_gt hx)
    simp [hx, hz]

private theorem compressed_physical_mass_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < ∫ x : ℝ in Ioi Real.pi, ‖compressedFeature κ x‖ ^ 2 := by
  rw [compressed_mass_Ioi_eq hκ]
  apply integral_pos_of_integrable_nonneg_nonzero
    ((compressedFeature_continuous hκ).norm.pow 2) (compressed_mass_integrable hκ)
    (fun x => sq_nonneg _) (x := Real.pi * Real.exp (κ / 2))
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (compressedFeature_center_ne hκ))

private theorem compressed_moment_ratio_bound {κ : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in Ioi Real.pi,
      (x / Real.pi) ^ (6 : ℕ) * ‖compressedFeature κ x‖ ^ 2) ≤
      Real.exp (9 * κ / 2) *
        (∫ x : ℝ in Ioi Real.pi, ‖compressedFeature κ x‖ ^ 2) := by
  rw [← integral_const_mul]
  apply integral_mono (compressed_sixth_integrable hκ).integrableOn
    ((compressed_mass_integrable hκ).const_mul _).integrableOn
  intro x
  by_cases hz : compressedFeature κ x = 0
  · simp [hz]
  · have hx := compressedFeature_support hκ hz
    have ha : 0 ≤ x / Real.pi :=
      div_nonneg (le_trans Real.pi_pos.le hx.1) Real.pi_pos.le
    have hb : x / Real.pi ≤ Real.exp (3 * κ / 4) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      simpa only [mul_comm] using hx.2
    have hc := pow_le_pow_left₀ ha hb 6
    have he : Real.exp (3 * κ / 4) ^ (6 : ℕ) = Real.exp (9 * κ / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      <;> ring
    rw [he] at hc
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

private theorem compressedFeature_zero_high {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x : ℝ} (hx : 4 * Real.pi ≤ x) : compressedFeature κ x = 0 := by
  by_contra hn
  have hs := (compressedFeature_support hκ hn).2
  have hl : 3 * κ / 4 < Real.log 4 := by
    linarith [three_quarters_lt_log_four]
  have he : Real.exp (3 * κ / 4) < 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mp hl
  nlinarith [mul_lt_mul_of_pos_left he Real.pi_pos]

private theorem compressed_terms_hasSum {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {x : ℝ} (hx : Real.pi ≤ x) :
    HasSum (fun k : ℕ => physicalTerm (compressedFeature κ) k x)
      (compressedFeature κ x) := by
  have ht (k : ℕ) (hk : k ≠ 0) : physicalTerm (compressedFeature κ) k x = 0 := by
    have hn : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
    have hn2 : (4 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by nlinarith
    have hy : 4 * Real.pi ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * x := by
      nlinarith [mul_le_mul_of_nonneg_right hn2 (le_trans Real.pi_pos.le hx)]
    simp only [physicalTerm, compressedFeature_zero_high hκ hκ1 hy, mul_zero]
  have hf : (fun k : ℕ => physicalTerm (compressedFeature κ) k x) =
      fun k : ℕ => if k = 0 then compressedFeature κ x else 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [physicalTerm]
    · simp [hk, ht k hk]
  rw [hf]
  exact hasSum_ite_eq 0 (compressedFeature κ x)

private theorem compressed_actualProfile_eq {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    actualGammaProfile (compressedFeature κ) = compressedProfile κ := by
  funext t
  by_cases ht : 0 ≤ t
  · have hxpos : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
    have hx : Real.pi ≤ Real.pi * Real.exp t := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.one_le_exp_iff.mpr ht) Real.pi_pos.le
    have hf : fullTheta (compressedFeature κ) (Real.pi * Real.exp t) =
        compressedFeature κ (Real.pi * Real.exp t) :=
      (compressed_terms_hasSum hκ hκ1 hx).tsum_eq
    have hl : Real.log ((Real.pi * Real.exp t) / Real.pi) = t := by
      rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
    have hr : (Real.pi * Real.exp t) ^ (9 / 4 : ℝ) *
        (Real.pi * Real.exp t) ^ (-9 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have hrc : (((Real.pi * Real.exp t) ^ (9 / 4 : ℝ) : ℝ) : ℂ) *
        (((Real.pi * Real.exp t) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hr
    rw [actualGammaProfile, if_pos ht, hf, compressedFeature, sourceOfProfile,
      if_pos hx, hl, ← mul_assoc, hrc, one_mul]
  · have hz : compressedProfile κ t = 0 :=
      compressed_zero_off hκ (fun h => by linarith [h.1])
    simp [actualGammaProfile, ht, hz]

private theorem compressed_profile_exponential_moments {κ : ℝ} (hκ : 0 < κ) (q : ℝ) :
    Integrable (fun t : ℝ => Real.exp (q * t) * ‖compressedProfile κ t‖ ^ 2) volume := by
  have hc : Continuous (fun t : ℝ => Real.exp (q * t) * ‖compressedProfile κ t‖ ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((compressed_continuous κ).norm.pow 2)
  have hs : HasCompactSupport (fun t : ℝ => Real.exp (q * t) *
      ‖compressedProfile κ t‖ ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra h
    exact ht (by simp [compressed_zero_off hκ h])
  exact hc.integrable_of_hasCompactSupport hs

private theorem compressed_profile_mass_moment {κ : ℝ} (hκ : 0 < κ) :
    (0 < ∫ t : ℝ, ‖compressedProfile κ t‖ ^ 2) ∧
    Integrable (fun t : ℝ => t * ‖compressedProfile κ t‖ ^ 2)
      (volume.restrict (Ioi 0)) ∧
    (0 < ∫ t : ℝ in Ioi 0, t * ‖compressedProfile κ t‖ ^ 2) := by
  let q : ℝ → ℝ := fun t => ‖compressedProfile κ t‖ ^ 2
  have hcq : Continuous q := (compressed_continuous κ).norm.pow 2
  have hsq : HasCompactSupport q := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra h
    exact ht (by simp [q, compressed_zero_off hκ h])
  have hiq : Integrable q volume := hcq.integrable_of_hasCompactSupport hsq
  have hp : 0 < ∫ t : ℝ, q t :=
    hcq.integral_pos_of_hasCompactSupport_nonneg_nonzero hsq (fun t => sq_nonneg _)
      (x := κ / 2) (by simp [q, compressed_center hκ])
  have hcs : Continuous (fun t : ℝ => t * q t) := continuous_id.mul hcq
  have hss : HasCompactSupport (fun t : ℝ => t * q t) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := κ / 4) (b := 3 * κ / 4))
    intro t ht
    by_contra h
    exact ht (by simp [q, compressed_zero_off hκ h])
  have his : Integrable (fun t : ℝ => t * q t) volume :=
    hcs.integrable_of_hasCompactSupport hss
  have hb (t : ℝ) : (κ / 4) * q t ≤ t * q t := by
    by_cases ht : t ∈ Icc (κ / 4) (3 * κ / 4)
    · exact mul_le_mul_of_nonneg_right ht.1 (sq_nonneg _)
    · simp [q, compressed_zero_off hκ ht]
  have hl : (κ / 4) * (∫ t : ℝ, q t) ≤ ∫ t : ℝ, t * q t := by
    simpa only [integral_const_mul] using integral_mono (hiq.const_mul _) his hb
  have he : (∫ t : ℝ in Ioi 0, t * q t) = ∫ t : ℝ, t * q t := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp [ht]
    · have hz : compressedProfile κ t = 0 :=
        compressed_zero_off hκ (fun h => ht (show 0 < t by linarith [h.1, hκ]))
      simp [ht, q, hz]
  refine ⟨hp, his.integrableOn, ?_⟩
  change 0 < ∫ t : ℝ in Ioi 0, t * q t
  rw [he]
  exact lt_of_lt_of_le (mul_pos (by positivity) hp) hl

private theorem compressed_not_form_domain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (c : ℝ) (hc : ∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) :
    ¬ originalGammaFormDomain c (compressedFeature κ) := by
  intro hGamma
  let q : ℝ → ℝ := fun ξ =>
    ‖unitarySourceFourier (actualGammaProfile (compressedFeature κ)) ξ‖ ^ 2
  have hq (ξ : ℝ) : 0 ≤ q ξ := sq_nonneg _
  have hFiniteGamma : Integrable
      (fun ξ : ℝ => (Symbol.gammaWeight ξ + c) * q ξ) volume := hGamma
  have hFiniteLog : HasFiniteIntegral (fun ξ : ℝ => max (Real.log |ξ|) 0 * q ξ) volume := by
    apply (hFiniteGamma.const_mul
      (Symbol.domainConstant * (1 + |c|))).hasFiniteIntegral.mono_nonneg
    · exact Eventually.of_forall fun ξ => mul_nonneg (le_max_right _ _) (hq ξ)
    · exact Eventually.of_forall fun ξ => by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right
            (Symbol.actualGammaWeight_shifted_log_bound c hc ξ) (hq ξ)
  have hlt : (∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 * q ξ)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ξ => mul_nonneg (le_max_right _ _) (hq ξ))).mp hFiniteLog
  have htop : (∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 * q ξ)) = ∞ := by
    dsimp [q]
    rw [compressed_actualProfile_eq hκ hκ1]
    exact compressed_positive_log_top hκ hκ1
  rw [htop] at hlt
  exact (lt_irrefl (∞ : ℝ≥0∞)) hlt

private theorem quarter_compression_bound : Real.exp (9 / 8 : ℝ) < 4 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mp
  rw [Real.log_four_eq]
  linarith [Real.log_two_gt_d9]

private theorem exists_cap_compression (K : ℝ) (hK : 1 < K) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ Real.exp (9 * κ / 2) < K := by
  by_cases h4 : 4 ≤ K
  · refine ⟨1 / 4, by norm_num, le_rfl, ?_⟩
    simpa only [show 9 * (1 / 4 : ℝ) / 2 = 9 / 8 by norm_num] using
      quarter_compression_bound.trans_le h4
  · let κ : ℝ := min (1 / 4 : ℝ) (Real.log K / 9)
    have hL : 0 < Real.log K := Real.log_pos hK
    have hk : 0 < κ := lt_min (by norm_num) (by positivity)
    have hkc : κ ≤ 1 / 4 := min_le_left _ _
    have hkl : κ ≤ Real.log K / 9 := min_le_right _ _
    refine ⟨κ, hk, hkc, ?_⟩
    calc
      Real.exp (9 * κ / 2) < Real.exp (Real.log K) :=
        Real.exp_lt_exp.mpr (by nlinarith [hkl])
      _ = K := Real.exp_log (by linarith)

/-- The compressed actual physical source meets every prescribed original
sixth-moment cap K>1 and escapes every admissible constant Gamma shift.
For K>=4, κ=1/4 gives logarithmic support [1/16,3/16] and
M/H<=exp(9/8)<4. -/
private theorem fixed_cap_escape_construct (K : ℝ) (hK : 1 < K) :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∀ x : ℝ, (F x).im = 0) ∧
      (∀ x : ℝ, Real.pi ≤ x → HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      Integrable (actualGammaProfile F) volume ∧
      MemLp (actualGammaProfile F) 2 volume ∧
      (∀ q : ℝ, Integrable
        (fun t : ℝ => Real.exp (q * t) * ‖actualGammaProfile F t‖ ^ 2) volume) ∧
      (0 < ∫ t : ℝ, ‖actualGammaProfile F t‖ ^ 2) ∧
      Integrable (fun t : ℝ => t * ‖actualGammaProfile F t‖ ^ 2)
        (volume.restrict (Ioi 0)) ∧
      (0 < ∫ t : ℝ in Ioi 0, t * ‖actualGammaProfile F t‖ ^ 2) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
      ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) <
        K * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      ((∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
        ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2)) = ∞) ∧
      (∀ c : ℝ, (∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) →
        ¬ originalGammaFormDomain c F) := by
  obtain ⟨κ, hk, hkc, hkK⟩ := exists_cap_compression K hK
  have hk1 : κ ≤ 1 := by linarith
  have he := compressed_actualProfile_eq hk hk1
  have hm := compressed_profile_mass_moment hk
  refine ⟨compressedFeature κ, compressed_original_h6 hk,
    compressedFeature_real κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    compressed_physical_mass_pos hk, ?_, ?_, compressed_not_form_domain hk hk1⟩
  · intro x hx
    exact compressed_terms_hasSum hk hk1 hx
  · rw [he]
    exact compressed_L1 hk
  · rw [he]
    exact compressed_profile_memLp hk
  · intro q
    rw [he]
    exact compressed_profile_exponential_moments hk q
  · rw [he]
    exact hm.1
  · rw [he]
    exact hm.2.1
  · rw [he]
    exact hm.2.2
  · exact lt_of_le_of_lt (compressed_moment_ratio_bound hk)
      (mul_lt_mul_of_pos_right hkK (compressed_physical_mass_pos hk))
  · rw [he]
    exact compressed_positive_log_top hk hk1


/-- Sharp original sixth-moment threshold for simultaneous escape from every
admissible constant shift of the actual Gamma form domain. The same witness
works for all shifts, including negative relative shifts with weight >= 1.
It retains literal physical H>0, full theta, actual profile L1/L2 and divergent
extended log-plus integral. The conclusion concerns form-domain membership;
it makes no assertion about the sign of the complete Weil energy or RH. -/
theorem actual_h6_gamma_domain_escape_iff (K : ℝ) :
    (∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∀ x : ℝ, (F x).im = 0) ∧
      (∀ x : ℝ, Real.pi ≤ x → HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      Integrable (actualGammaProfile F) volume ∧
      MemLp (actualGammaProfile F) 2 volume ∧
      (∀ q : ℝ, Integrable
        (fun t : ℝ => Real.exp (q * t) * ‖actualGammaProfile F t‖ ^ 2) volume) ∧
      (0 < ∫ t : ℝ, ‖actualGammaProfile F t‖ ^ 2) ∧
      Integrable (fun t : ℝ => t * ‖actualGammaProfile F t‖ ^ 2)
        (volume.restrict (Ioi 0)) ∧
      (0 < ∫ t : ℝ in Ioi 0, t * ‖actualGammaProfile F t‖ ^ 2) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
      ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) <
        K * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      ((∫⁻ ξ : ℝ, ENNReal.ofReal (max (Real.log |ξ|) 0 *
        ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2)) = ∞) ∧
      (∀ c : ℝ, (∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) →
        ¬ originalGammaFormDomain c F)) ↔ 1 < K := by
  constructor
  · rintro ⟨F, hH6, _, _, _, _, _, _, _, _, hH, hcap, _, _⟩
    have hmass : Integrable (fun x : ℝ => ‖F x‖ ^ (2 : ℕ))
        (volume.restrict (Ioi Real.pi)) :=
      hH6.1.integrable_norm_pow (p := 2) (by norm_num)
    have hHM : (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ≤
        ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2 := by
      apply integral_mono_ae hmass hH6.2
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : Real.pi < x := hx
      have hr : (1 : ℝ) ≤ x / Real.pi := by
        apply (le_div_iff₀ Real.pi_pos).mpr
        simpa only [one_mul] using hx'.le
      have hp : (1 : ℝ) ≤ (x / Real.pi) ^ (6 : ℕ) := one_le_pow₀ hr
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (sq_nonneg ‖F x‖)
    have hHK := hHM.trans_lt hcap
    nlinarith [hH]
  · intro hK
    exact fixed_cap_escape_construct K hK

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
