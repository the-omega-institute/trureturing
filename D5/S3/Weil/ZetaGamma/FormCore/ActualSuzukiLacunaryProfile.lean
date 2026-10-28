/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-domain-refutation)
   anchors: []
   utility: none
   digest: Explicit lacunary profile with divergent actual positive-log Fourier energy. -/

import D5.S3.Weil.ZetaCore.PaperFT
import Mathlib.Analysis.Real.Pi.Bounds
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

theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  unfold coeff
  positivity

theorem coeff_hasSum : HasSum coeff 1 := by
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

theorem tent_zero_of_quarter_le {s : ℝ} (hs : 1 / 4 ≤ |s|) :
    tent s = 0 := by
  apply max_eq_right
  linarith

theorem profile_continuous : Continuous counterProfile := by
  have h : Continuous counterProfileReal :=
    (tent_continuous.comp (continuous_id.sub continuous_const)).mul
      carrierSeries_continuous
  exact Complex.continuous_ofReal.comp h

theorem profile_zero_off {t : ℝ}
    (ht : t ∉ Icc (1 / 4 : ℝ) (3 / 4)) : counterProfile t = 0 := by
  have hs : (1 / 4 : ℝ) ≤ |t - 1 / 2| := by
    by_contra h
    have ha := abs_lt.mp (lt_of_not_ge h)
    apply ht
    constructor <;> linarith [ha.1, ha.2]
  simp only [counterProfile, counterProfileReal, tent_zero_of_quarter_le hs,
    zero_mul, Complex.ofReal_zero]

theorem profile_center : counterProfile (1 / 2) = 1 := by
  have h : carrierSeries (1 / 2) = 1 := by
    simpa only [carrierSeries, sub_self, mul_zero, Real.cos_zero, mul_one] using
      coeff_hasSum.tsum_eq
  simp only [counterProfile, counterProfileReal, h]
  norm_num [tent]

theorem three_quarters_lt_log_four : (3 / 4 : ℝ) < Real.log 4 := by
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

def tentSourceHat (ξ : ℝ) : ℝ :=
  (1 / (4 * Real.sqrt (2 * Real.pi))) * Real.sinc (ξ / 8) ^ 2

def spectralTerm (n : ℕ) (ξ : ℝ) : ℝ :=
  (coeff n / 2) *
    (tentSourceHat (ξ - frequency n) + tentSourceHat (ξ + frequency n))

private def spectralAmplitude (ξ : ℝ) : ℝ := ∑' n : ℕ, spectralTerm n ξ

def positiveBand (n : ℕ) : Set ℝ :=
  Icc (frequency n - 1) (frequency n + 1)

theorem coeff_positive (n : ℕ) : 0 < coeff n := by
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

theorem positiveBands_disjoint : Pairwise (Disjoint on positiveBand) := by
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

theorem coeff_sq_log_frequency (n : ℕ) :
    coeff n ^ 2 * Real.log (frequency n) = 1 := by
  rw [log_frequency]
  dsimp [coeff]
  calc
    ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 * (4 : ℝ) ^ (n + 1) =
        ((1 / 2 : ℝ) ^ 2) ^ (n + 1) * (4 : ℝ) ^ (n + 1) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (n + 1) 2]
    _ = (((1 / 2 : ℝ) ^ 2) * 4) ^ (n + 1) := by rw [mul_pow]
    _ = 1 := by norm_num

theorem tentSourceHat_nonneg (ξ : ℝ) : 0 ≤ tentSourceHat ξ := by
  dsimp [tentSourceHat]
  positivity

private theorem tentSourceHat_upper (ξ : ℝ) :
    tentSourceHat ξ ≤ 1 / (4 * Real.sqrt (2 * Real.pi)) := by
  have hsinc := abs_le.mp (Real.abs_sinc_le_one (ξ / 8))
  have hsq : Real.sinc (ξ / 8) ^ 2 ≤ 1 := by nlinarith [hsinc.1, hsinc.2]
  exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans_eq (mul_one _)

theorem tentSourceHat_lower_unit {ξ : ℝ} (hξ : |ξ| ≤ 1) :
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

theorem spectralTerm_nonneg (n : ℕ) (ξ : ℝ) : 0 ≤ spectralTerm n ξ := by
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

theorem positiveBand_log_lower (n : ℕ) {ξ : ℝ}
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

def sourcePhase (ξ t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))

def spatialTerm (n : ℕ) (t : ℝ) : ℂ :=
  ((coeff n * tent (t - 1 / 2) *
    Real.cos (frequency n * (t - 1 / 2)) : ℝ) : ℂ)

theorem sourcePhase_norm (ξ t : ℝ) : ‖sourcePhase ξ t‖ = 1 := by
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

theorem unitarySourceFourier_eq_integral (u : ℝ → ℂ) (ξ : ℝ) :
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

theorem actual_spatial_series_hasSum (t : ℝ) :
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

theorem actual_kernel_term_norm_bound (ξ t : ℝ) (n : ℕ) :
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

theorem actual_spatial_term_fourier (n : ℕ) (ξ : ℝ) :
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
theorem actual_counterProfile_positive_log_top :
    (∫⁻ ξ : ℝ, ENNReal.ofReal
      (max (Real.log |ξ|) 0 * ‖unitarySourceFourier counterProfile ξ‖ ^ 2)) = ∞ := by
  simp_rw [actual_counterProfile_fourier_norm_sq]
  exact spectralAmplitude_log_lintegral_top

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
