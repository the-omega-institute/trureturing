/- GID: D5/S3/Analytic/PowerSeries/WeightedChargeKernelCore
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Gaussian coefficient curves generate the weighted central charge kernel. -/
/-
SPDX-License-Identifier: Apache-2.0
Weighted central-charge coefficient core, 2026-10-26.

Carrier: w_k = (k+1)^2 d_k in ordinary lp (fun _ : ℕ => ℝ) 2.
Charge: a_k = z_k/(k+1)^2, L(w) = inner a w = sum z_k d_k.
No new Banach-space structure, Laguerre completeness, or closed synthesis
image is postulated. In particular the restricted X4 synthesis image need
not be closed in the original physical H.

Repository/Mathlib APIs reused: lp.hasSum_single, lp.inner_single_right,
innerSL, ContinuousLinearMap.smulRight, Submodule.topologicalClosure_minimal,
ContinuousMultilinearMap.mkPiRing, FormalMultilinearSeries.sum_mem,
FormalMultilinearSeries.le_radius_of_summable_norm, and the accepted
RHGaussianDilationCore.powerSeries_coeff_mem_of_positive_values.

The actual reflected Gaussian consumer supplies the following scalar data:
  z_k = normalizedCentralMellin(2k)/normalizedCentralMellin(0),
  z0=1, abs z_k<=1;
  c_k = 1/N_(2k), c_k != 0, abs c_k <= (1/N0)*(9/2)^k;
  for 0<t<1/36, n>=1, a=log((1+sqrt t)/(1-sqrt t))/2,
  d_t(n) = finiteGaussianNormalizedCoefficient [1,1,-2] [a,-a,0] (2n)
           / (2*gaussianSiteAmplitude a) = c_n*t^n;
  HasSum (fun n => z_n*d_t(n)) 0 from the actual finite-source charge.
The final theorem then proves the full series identity, including coordinate
zero, by charge uniqueness; no beta/binomial constant-term proof is needed.
Cross-module use of existing private site_q_neg and site_amplitude_neg needs
canonical visibility migration with their unchanged proofs, rather than
reproof. No density or coefficient-membership assertion is assumed here.

The final theorem constructs the weighted Hilbert carrier and proves the full
charge-kernel core from scalar tail data, without any assumed density.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import D5.S3.Analytic.PowerSeries.PositiveParameterClosedSubmodule

/-! Weighted Gaussian coefficient curves and the continuous central-charge kernel. -/

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped Topology NNReal ENNReal

namespace RHGaussianDilationCore

abbrev GaussianCoeffSpace := lp (fun _ : ℕ => ℝ) 2

def coeffWeight (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

private theorem coeffWeight_pos (n : ℕ) : 0 < coeffWeight n := by
  unfold coeffWeight
  positivity

private theorem inv_coeffWeight_memℓp :
    Memℓp (fun n : ℕ => 1 / coeffWeight n) 2 := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 4) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        ((Real.summable_one_div_nat_pow (p := 4)).mpr (by decide))
  apply memℓp_gen
  convert hs using 1
  funext n
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_div, norm_one,
    coeffWeight, norm_pow, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1),
    div_pow, one_pow, ← pow_mul]

/-- The actual central-charge covector in the weighted coordinates. -/
def gaussianChargeVector (z : ℕ → ℝ) (hz : ∀ n, |z n| ≤ 1) : GaussianCoeffSpace :=
  ⟨fun n => z n / coeffWeight n,
    inv_coeffWeight_memℓp.mono (by
      intro n
      rw [norm_div, Real.norm_eq_abs,
        Real.norm_of_nonneg (coeffWeight_pos n).le]
      exact div_le_div_of_nonneg_right (hz n) (coeffWeight_pos n).le)⟩

@[simp] private theorem gaussianChargeVector_apply
    (z : ℕ → ℝ) (hz : ∀ n, |z n| ≤ 1) (n : ℕ) :
    gaussianChargeVector z hz n = z n / coeffWeight n := rfl

def coeffBasis (n : ℕ) : GaussianCoeffSpace := lp.single 2 n 1

def coeffCharge (a : GaussianCoeffSpace) : GaussianCoeffSpace →L[ℝ] ℝ :=
  innerSL ℝ a

@[simp] private theorem coeffCharge_basis (a : GaussianCoeffSpace) (n : ℕ) :
    coeffCharge a (coeffBasis n) = a n := by
  simp [coeffCharge, coeffBasis, innerSL_apply_apply, lp.inner_single_right,
    Real.inner_apply]

def repairedCoeffBasis (a : GaussianCoeffSpace) (n : ℕ) : GaussianCoeffSpace :=
  coeffBasis n - a n • coeffBasis 0

def coeffRepair (a : GaussianCoeffSpace) :
    GaussianCoeffSpace →L[ℝ] GaussianCoeffSpace :=
  ContinuousLinearMap.id ℝ GaussianCoeffSpace - (coeffCharge a).smulRight (coeffBasis 0)

private theorem repairedCoeffBasis_mem_ker (a : GaussianCoeffSpace)
    (ha : a 0 = 1) (n : ℕ) : repairedCoeffBasis a n ∈ (coeffCharge a).ker := by
  change coeffCharge a (coeffBasis n - a n • coeffBasis 0) = 0
  rw [map_sub, map_smul, coeffCharge_basis, coeffCharge_basis, ha]
  simp

/-- Continuous repair of the standard coordinate expansion gives density of
the charge-zero directions. The nonzero scalars allow actual normalizations. -/
private theorem closedSpan_scaled_repairedBasis_eq_ker
    (a : GaussianCoeffSpace) (ha : a 0 = 1)
    (b : ℕ → ℝ) (hb : ∀ n, b n ≠ 0) :
    (Submodule.span ℝ (Set.range (fun n => b n • repairedCoeffBasis a n))).topologicalClosure =
      (coeffCharge a).ker := by
  let K : Submodule ℝ GaussianCoeffSpace :=
    (Submodule.span ℝ (Set.range (fun n => b n • repairedCoeffBasis a n))).topologicalClosure
  have hK : IsClosed (K : Set GaussianCoeffSpace) :=
    (Submodule.span ℝ (Set.range (fun n => b n • repairedCoeffBasis a n))).isClosed_topologicalClosure
  have hdir : ∀ n, repairedCoeffBasis a n ∈ K := by
    intro n
    have hu : b n • repairedCoeffBasis a n ∈ K :=
      (Submodule.span ℝ (Set.range (fun n => b n • repairedCoeffBasis a n))).le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self n))
    have h := K.smul_mem (b n)⁻¹ hu
    simpa only [smul_smul, inv_mul_cancel₀ (hb n), one_smul] using h
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact (coeffCharge a).ker.smul_mem _ (repairedCoeffBasis_mem_ker a ha n)
    · exact (coeffCharge a).isClosed_ker
  · intro w hw
    change coeffCharge a w = 0 at hw
    have hPw : coeffRepair a w = w := by simp [coeffRepair, hw]
    have hsum : HasSum (fun n => coeffRepair a (lp.single 2 n (w n))) w := by
      simpa only [hPw] using
        (lp.hasSum_single ENNReal.ofNat_ne_top w).mapL (coeffRepair a)
    apply hK.mem_of_tendsto hsum
    apply Filter.Eventually.of_forall
    intro s
    apply K.sum_mem
    intro n _
    have hsingle : lp.single 2 n (w n) = w n • coeffBasis n := by
      simpa only [coeffBasis, smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : ℕ => ℝ) 2 n (w n) (1 : ℝ))
    have hPe : coeffRepair a (coeffBasis n) = repairedCoeffBasis a n := by
      simp [coeffRepair, repairedCoeffBasis]
    rw [hsingle, map_smul, hPe]
    exact K.smul_mem _ (hdir n)

def positiveCurveSpan (f : ℝ → GaussianCoeffSpace) (r : ℝ) :
    Submodule ℝ GaussianCoeffSpace :=
  (Submodule.span ℝ (f '' Set.Ioo 0 r)).topologicalClosure

/-- A vector-valued power series with these coefficients recovers the entire
charge kernel from arbitrarily short positive parameter intervals. -/
private theorem positive_series_core_eq_ker
    (a : GaussianCoeffSpace) (ha : a 0 = 1)
    (b : ℕ → ℝ) (hb : ∀ n, b n ≠ 0)
    (p : FormalMultilinearSeries ℝ ℝ GaussianCoeffSpace)
    (hcoeff : ∀ n, p.coeff n = b n • repairedCoeffBasis a n)
    (hrad : 0 < p.radius) {r : ℝ} (hr : 0 < r) :
    positiveCurveSpan p.sum r = (coeffCharge a).ker := by
  let K := positiveCurveSpan p.sum r
  have hK : IsClosed (K : Set GaussianCoeffSpace) :=
    (Submodule.span ℝ (p.sum '' Set.Ioo 0 r)).isClosed_topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨t, _, rfl⟩
      apply FormalMultilinearSeries.sum_mem (coeffCharge a).isClosed_ker p t
      intro n
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hcoeff]
      exact (coeffCharge a).ker.smul_mem _
        ((coeffCharge a).ker.smul_mem _ (repairedCoeffBasis_mem_ker a ha n))
    · exact (coeffCharge a).isClosed_ker
  · rw [← closedSpan_scaled_repairedBasis_eq_ker a ha b hb]
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      change b n • repairedCoeffBasis a n ∈ K
      rw [← hcoeff n]
      exact powerSeries_coeff_mem_of_positive_values K hK
        (p.hasFPowerSeriesOnBall hrad).hasFPowerSeriesAt hr
        (fun t ht htr =>
          (Submodule.span ℝ (p.sum '' Set.Ioo 0 r)).le_topologicalClosure
            (Submodule.subset_span ⟨t, ⟨ht, htr⟩, rfl⟩)) n
    · exact hK

/-- The exact weighted coordinates of e_n-z_n e_0 in physical coefficients. -/
def gaussianCoeffDirection (z : ℕ → ℝ) (n : ℕ) : GaussianCoeffSpace :=
  coeffWeight n • coeffBasis n - z n • coeffBasis 0

private theorem gaussianCoeffDirection_eq_scaled_repaired
    (z : ℕ → ℝ) (hz : ∀ n, |z n| ≤ 1) (n : ℕ) :
    gaussianCoeffDirection z n =
      coeffWeight n • repairedCoeffBasis (gaussianChargeVector z hz) n := by
  have hcancel : coeffWeight n * (z n / coeffWeight n) = z n := by
    field_simp [ne_of_gt (coeffWeight_pos n)]
    <;> ring
  simp only [gaussianCoeffDirection, repairedCoeffBasis, smul_sub,
    smul_smul, gaussianChargeVector_apply, hcancel]

private theorem coeffWeight_le_four_pow (n : ℕ) : coeffWeight n ≤ (4 : ℝ) ^ n := by
  have hnat : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
    intro m
    induction m with
    | zero => norm_num
    | succ m hm =>
      calc
        m + 1 + 1 ≤ (m + 1) + (m + 1) := by omega
        _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add hm hm
        _ = 2 ^ (m + 1) := by ring
  have hreal : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat n
  calc
    coeffWeight n ≤ ((2 : ℝ) ^ n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hreal 2
    _ = (4 : ℝ) ^ n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num

private theorem gaussianCoeffDirection_norm_le (z : ℕ → ℝ)
    (hz : ∀ n, |z n| ≤ 1) (n : ℕ) :
    ‖gaussianCoeffDirection z n‖ ≤ 2 * (4 : ℝ) ^ n := by
  have he : ∀ k, ‖coeffBasis k‖ = 1 := by
    intro k
    simp [coeffBasis, lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]
  have hone : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  calc
    ‖gaussianCoeffDirection z n‖ ≤
        ‖coeffWeight n • coeffBasis n‖ + ‖z n • coeffBasis 0‖ := norm_sub_le _ _
    _ = coeffWeight n + |z n| := by
      simp only [norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_pos (coeffWeight_pos n)]
    _ ≤ coeffWeight n + 1 := add_le_add_right (hz n) _
    _ ≤ 2 * (4 : ℝ) ^ n := by linarith [coeffWeight_le_four_pow n]

def gaussianCoeff (z c : ℕ → ℝ) (n : ℕ) : GaussianCoeffSpace :=
  c n • gaussianCoeffDirection z n

/-- mkPiRing supports vector coefficients; ofScalars does not. -/
def gaussianSeries (z c : ℕ → ℝ) : FormalMultilinearSeries ℝ ℝ GaussianCoeffSpace :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (gaussianCoeff z c n)

@[simp] private theorem gaussianSeries_coeff (z c : ℕ → ℝ) (n : ℕ) :
    (gaussianSeries z c).coeff n = gaussianCoeff z c n := by
  simp [gaussianSeries, FormalMultilinearSeries.coeff]

private theorem gaussianCoeff_norm_le (z c : ℕ → ℝ)
    (hz : ∀ n, |z n| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n) (n : ℕ) :
    ‖gaussianCoeff z c n‖ ≤ (2 * C) * (18 : ℝ) ^ n := by
  calc
    ‖gaussianCoeff z c n‖ = |c n| * ‖gaussianCoeffDirection z n‖ := by
      simp only [gaussianCoeff, norm_smul, Real.norm_eq_abs]
    _ ≤ (C * (9 / 2 : ℝ) ^ n) * (2 * (4 : ℝ) ^ n) :=
      mul_le_mul (hc n) (gaussianCoeffDirection_norm_le z hz n)
        (norm_nonneg _) (by positivity)
    _ = (2 * C) * (18 : ℝ) ^ n := by rw [show (18 : ℝ) = 9 / 2 * 4 by norm_num, mul_pow]; ring

private theorem gaussianSeries_radius_ge (z c : ℕ → ℝ)
    (hz : ∀ n, |z n| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n) :
    ((1 / 36 : ℝ≥0) : ℝ≥0∞) ≤ (gaussianSeries z c).radius := by
  let r : ℝ≥0 := 1 / 36
  have hs : Summable (fun n => ‖gaussianSeries z c n‖ * (r : ℝ) ^ n) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity)
      (g := fun n => ‖gaussianSeries z c n‖ * (r : ℝ) ^ n)
      (f := fun n => (2 * C) * (1 / 2 : ℝ) ^ n)
    · intro n
      calc
        ‖gaussianSeries z c n‖ * (r : ℝ) ^ n ≤
            ((2 * C) * (18 : ℝ) ^ n) * (r : ℝ) ^ n := by
          gcongr
          simpa only [gaussianSeries, ContinuousMultilinearMap.norm_mkPiRing] using
            gaussianCoeff_norm_le z c hz hC hc n
        _ = (2 * C) * (1 / 2 : ℝ) ^ n := by
          rw [mul_assoc, ← mul_pow]
          congr 2
          norm_num [r]
    · exact summable_geometric_two.mul_left (2 * C)
  exact (gaussianSeries z c).le_radius_of_summable_norm hs

/-- Complete coefficient-space core, with the exact atom identity left to its
physical supplier. c_n=1/N_(2n), C=1/N0 give the actual normalization. -/
private theorem weighted_gaussian_coefficient_core
    (z c : ℕ → ℝ) (hz0 : z 0 = 1) (hz : ∀ n, |z n| ≤ 1)
    (hc0 : ∀ n, c n ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n)
    {r : ℝ} (hr : 0 < r) :
    positiveCurveSpan (gaussianSeries z c).sum r =
      (coeffCharge (gaussianChargeVector z hz)).ker := by
  have ha : gaussianChargeVector z hz 0 = 1 := by
    simp [gaussianChargeVector_apply, coeffWeight, hz0]
  apply positive_series_core_eq_ker (gaussianChargeVector z hz) ha
    (fun n => c n * coeffWeight n)
    (fun n => mul_ne_zero (hc0 n) (ne_of_gt (coeffWeight_pos n)))
    (gaussianSeries z c)
  · intro n
    rw [gaussianSeries_coeff, gaussianCoeff,
      gaussianCoeffDirection_eq_scaled_repaired z hz n, smul_smul]
  · exact lt_of_lt_of_le (by norm_num) (gaussianSeries_radius_ge z c hz hC hc)
  · exact hr

/-- The charge and all nonzero coordinates determine a vector, because the
charge of the zeroth unit vector equals one. This is the zeroth-coordinate
identification needed for the actual Gaussian source. -/
private theorem eq_of_charge_and_tail
    (a : GaussianCoeffSpace) (ha : a 0 = 1) (x y : GaussianCoeffSpace)
    (hcharge : coeffCharge a x = coeffCharge a y)
    (htail : ∀ n : ℕ, n ≠ 0 → x n = y n) : x = y := by
  have hdiff : x - y = (x 0 - y 0) • coeffBasis 0 := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp [coeffBasis]
    · simp [coeffBasis, hn, htail n hn]
  have hc : coeffCharge a (x - y) = 0 := by rw [map_sub, hcharge, sub_self]
  have hzero : x 0 - y 0 = 0 := by
    simpa only [hdiff, map_smul, coeffCharge_basis, ha, smul_eq_mul, mul_one] using hc
  ext n
  by_cases hn : n = 0
  · subst n
    exact sub_eq_zero.mp hzero
  · exact htail n hn

/-- Exact physical scalar HasSum is enough to identify the Hilbert-space
charge. No unjustified interchange of an integral and infinite series occurs. -/
private theorem coeffCharge_eq_of_actual_hasSum
    (z : ℕ → ℝ) (hz : ∀ n, |z n| ≤ 1) (d : ℕ → ℝ)
    (w : GaussianCoeffSpace) (hw : ∀ n, w n = coeffWeight n * d n)
    {M : ℝ} (hd : HasSum (fun n => z n * d n) M) :
    coeffCharge (gaussianChargeVector z hz) w = M := by
  have hi := lp.hasSum_inner (𝕜 := ℝ) (gaussianChargeVector z hz) w
  have hinner : HasSum (fun n => z n * d n)
      (coeffCharge (gaussianChargeVector z hz) w) := by
    convert hi using 1
    · funext n
      rw [Real.inner_apply, gaussianChargeVector_apply, hw]
      field_simp [ne_of_gt (coeffWeight_pos n)]
      <;> ring
    · simp only [coeffCharge, innerSL_apply_apply]
  exact hinner.unique hd

private theorem gaussianSeries_hasSum_small
    (z c : ℕ → ℝ) (hz : ∀ n, |z n| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n)
    {t : ℝ} (ht : 0 < t) (htsmall : t < 1 / 36) :
    HasSum (fun n => gaussianSeries z c n (fun _ => t)) ((gaussianSeries z c).sum t) := by
  apply (gaussianSeries z c).hasSum
  have hball : t ∈ Metric.eball (0 : ℝ) (((1 / 36 : ℝ≥0) : ℝ≥0∞)) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_pos ht]
    exact htsmall
  exact lt_of_lt_of_le hball (gaussianSeries_radius_ge z c hz hC hc)

/-- Every positive-index coordinate of the candidate curve is a single
power-series term; this uses the continuous coordinate evaluation map. -/
private theorem gaussianSeries_tail_coordinate
    (z c : ℕ → ℝ) (hz : ∀ n, |z n| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n)
    {t : ℝ} (ht : 0 < t) (htsmall : t < 1 / 36)
    (n : ℕ) (hn : n ≠ 0) :
    (gaussianSeries z c).sum t n = coeffWeight n * (c n * t ^ n) := by
  have heval := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).hasSum
    (gaussianSeries_hasSum_small z c hz hC hc ht htsmall)
  change HasSum (fun m => (gaussianSeries z c m (fun _ => t)) n)
    ((gaussianSeries z c).sum t n) at heval
  have hterm (m : ℕ) : (gaussianSeries z c m (fun _ => t)) n =
      t ^ m * (c m * (coeffWeight m * coeffBasis m n - z m * coeffBasis 0 n)) := by
    simp only [gaussianSeries, ContinuousMultilinearMap.mkPiRing_apply,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  apply heval.unique
  convert hasSum_ite_eq n (coeffWeight n * (c n * t ^ n)) using 1
  funext m
  rw [hterm m]
  by_cases hmn : m = n
  · subst m
    simp [coeffBasis, Pi.single_apply, hn, mul_comm, mul_left_comm, mul_assoc]
  · simp [coeffBasis, Pi.single_apply, hn, hmn, Ne.symm hmn]

/-- Actual-curve bridge with a minimal physical supplier contract. The raw
coefficient curve d is determined from the literal finite Gaussian source.
Only positive-index coefficient formulas and actual charge HasSum are needed;
the zeroth-coordinate formula and analytic series identity are conclusions.
There is no assumed density, basis completeness, or coefficient-membership
premise. r<=1/36 is an explicit convergence condition. -/
private theorem actual_curve_core_of_tail_coefficients
    (z c : ℕ → ℝ) (hz0 : z 0 = 1) (hz : ∀ n, |z n| ≤ 1)
    (hc0 : ∀ n, c n ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n)
    (f : ℝ → GaussianCoeffSpace) (d : ℝ → ℕ → ℝ)
    {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 36)
    (hcoordinates : ∀ t, 0 < t → t < r →
      ∀ n, f t n = coeffWeight n * d t n)
    (hcharge : ∀ t, 0 < t → t < r → HasSum (fun n => z n * d t n) 0)
    (htail : ∀ t, 0 < t → t < r → ∀ n : ℕ, n ≠ 0 → d t n = c n * t ^ n) :
    positiveCurveSpan f r = (coeffCharge (gaussianChargeVector z hz)).ker := by
  have ha : gaussianChargeVector z hz 0 = 1 := by
    simp [gaussianChargeVector_apply, coeffWeight, hz0]
  have hcurve : ∀ t, 0 < t → t < r → f t = (gaussianSeries z c).sum t := by
    intro t ht htr
    apply eq_of_charge_and_tail (gaussianChargeVector z hz) ha
    · have hf := coeffCharge_eq_of_actual_hasSum z hz (d t) (f t)
        (hcoordinates t ht htr) (hcharge t ht htr)
      have hp : (gaussianSeries z c).sum t ∈
          (coeffCharge (gaussianChargeVector z hz)).ker := by
        apply FormalMultilinearSeries.sum_mem
          (coeffCharge (gaussianChargeVector z hz)).isClosed_ker
        intro n
        rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
          gaussianSeries_coeff, gaussianCoeff,
          gaussianCoeffDirection_eq_scaled_repaired z hz n]
        exact (coeffCharge (gaussianChargeVector z hz)).ker.smul_mem _
          ((coeffCharge (gaussianChargeVector z hz)).ker.smul_mem _
            ((coeffCharge (gaussianChargeVector z hz)).ker.smul_mem _
              (repairedCoeffBasis_mem_ker _ ha n)))
      change coeffCharge (gaussianChargeVector z hz) ((gaussianSeries z c).sum t) = 0 at hp
      exact hf.trans hp.symm
    · intro n hn
      rw [hcoordinates t ht htr n, htail t ht htr n hn,
        gaussianSeries_tail_coordinate z c hz hC hc ht (lt_of_lt_of_le htr hrsmall) n hn]
  have himage : f '' Set.Ioo 0 r = (gaussianSeries z c).sum '' Set.Ioo 0 r := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, (hcurve t ht.1 ht.2).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, hcurve t ht.1 ht.2⟩
  rw [positiveCurveSpan, himage]
  exact weighted_gaussian_coefficient_core z c hz0 hz hc0 hC hc hr

/-- The scalar actual coefficients themselves have a weighted Hilbert carrier;
there is no weighted-space membership assumption. The nonzero coordinates are
the convergent series, and their single remaining coordinate is a finite-rank
correction. The actual zero-charge HasSum removes that correction via the
preceding identification theorem. -/
theorem weighted_charge_kernel_core_of_scalar_curve
    (z c : ℕ → ℝ) (hz0 : z 0 = 1) (hz : ∀ n, |z n| ≤ 1)
    (hc0 : ∀ n, c n ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C * (9 / 2 : ℝ) ^ n)
    (d : ℝ → ℕ → ℝ) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 36)
    (hcharge : ∀ t, 0 < t → t < r → HasSum (fun n => z n * d t n) 0)
    (htail : ∀ t, 0 < t → t < r → ∀ n : ℕ, n ≠ 0 → d t n = c n * t ^ n) :
    ∃ f : ℝ → GaussianCoeffSpace,
      (∀ t, 0 < t → t < r → ∀ n, f t n = coeffWeight n * d t n) ∧
      positiveCurveSpan f r = (coeffCharge (gaussianChargeVector z hz)).ker := by
  let f : ℝ → GaussianCoeffSpace := fun t =>
    (gaussianSeries z c).sum t +
      (d t 0 - (gaussianSeries z c).sum t 0) • coeffBasis 0
  have hcoordinates : ∀ t, 0 < t → t < r →
      ∀ n, f t n = coeffWeight n * d t n := by
    intro t ht htr n
    by_cases hn : n = 0
    · subst n
      change (gaussianSeries z c).sum t 0 +
        (d t 0 - (gaussianSeries z c).sum t 0) * coeffBasis 0 0 = coeffWeight 0 * d t 0
      simp [coeffBasis, coeffWeight]
      <;> ring
    · have hp := gaussianSeries_tail_coordinate z c hz hC hc ht
        (lt_of_lt_of_le htr hrsmall) n hn
      simp only [f, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
        coeffBasis, lp.single_apply, Pi.single_eq_of_ne hn, smul_zero, add_zero]
      rw [hp, htail t ht htr n hn]
  exact ⟨f, hcoordinates,
    actual_curve_core_of_tail_coefficients z c hz0 hz hc0 hC hc f d hr hrsmall
      hcoordinates hcharge htail⟩

end RHGaussianDilationCore
