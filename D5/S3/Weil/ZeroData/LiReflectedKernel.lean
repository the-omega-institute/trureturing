/- GID: D5/S3/Weil/ZeroData/LiReflectedKernel
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/LiReflectedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reflected Li kernels have a summable quadratic tail and converge uniformly on a fixed disk. -/

import D5.S3.Weil.ZeroData.LiZeroSumConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

/-! Reflection cancels the first-order reciprocal-zero terms in the Li
resolvent. The resulting quadratic tail is summable without a critical-line
hypothesis. The conclusions concern convergence, not coefficient identification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZeroData.LiReflectedKernel

open Complex Filter
open scoped Topology BigOperators
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

private def ratio (rho : ℂ) : ℂ := 1 - 1 / rho

def reflectedLiKernel (Z : ZeroData) (k : ℕ) (z : ℂ) : ℂ :=
  (Z.multiplicity k : ℂ) / 2 *
    (2 * (1 - z)⁻¹ - ratio (Z.zero k) * (1 - ratio (Z.zero k) * z)⁻¹ -
      ratio (1 - Z.zero k) * (1 - ratio (1 - Z.zero k) * z)⁻¹)

private theorem zero_ne (Z : ZeroData) (k : ℕ) :
    Z.zero k ≠ 0 ∧ 1 - Z.zero k ≠ 0 := by
  have h := (Z.zero_isNontrivial k).2
  constructor
  · intro he
    rw [he] at h
    norm_num at h
  · intro he
    have he' : Z.zero k = 1 := (sub_eq_zero.mp he).symm
    rw [he'] at h
    norm_num at h

private theorem ratio_relations (rho : ℂ) (h0 : rho ≠ 0) (h1 : 1 - rho ≠ 0) :
    ratio rho * ratio (1 - rho) = 1 ∧
      ratio rho + ratio (1 - rho) = 2 - (rho * (1 - rho))⁻¹ := by
  dsimp [ratio]
  constructor <;> field_simp [h0, h1] <;> ring

private theorem denominator_identity (q r x z : ℂ)
    (hp : q * r = 1) (hs : q + r = 2 - x) :
    (1 - q * z) * (1 - r * z) = (1 - z) ^ 2 + x * z := by
  calc
    _ = 1 - (q + r) * z + (q * r) * z ^ 2 := by ring
    _ = _ := by rw [hp, hs]; ring

private theorem kernel_collapse (q r x z : ℂ)
    (hp : q * r = 1) (hs : q + r = 2 - x)
    (hz : 1 - z ≠ 0) (hd : (1 - z) ^ 2 + x * z ≠ 0) :
    2 * (1 - z)⁻¹ - q * (1 - q * z)⁻¹ - r * (1 - r * z)⁻¹ =
      x * (1 + z) / ((1 - z) * ((1 - z) ^ 2 + x * z)) := by
  have he := denominator_identity q r x z hp hs
  have hprod : (1 - q * z) * (1 - r * z) ≠ 0 := by rwa [he]
  have hq := (mul_ne_zero_iff.mp hprod).1
  have hr := (mul_ne_zero_iff.mp hprod).2
  rw [← he]
  field_simp [hz, hq, hr]
  linear_combination -(1 + z) * hs + 2 * z * hp

private theorem gamma_product (Z : ZeroData) (k : ℕ) :
    Z.zero k * (1 - Z.zero k) = (Z.gamma k) ^ 2 + 1 / 4 := by
  rw [Z.zero_eq_critical_add_I_mul_gamma]
  simp only [D5.S3.Weil.Convention.criticalAbscissa]
  ring_nf
  norm_num [Complex.I_sq]

private theorem inverse_product_bound (Z : ZeroData) (k : ℕ)
    (hk : 2 ≤ ‖Z.gamma k‖) :
    ‖(Z.zero k * (1 - Z.zero k))⁻¹‖ ≤ 1 / 2 ∧
      ‖(Z.zero k * (1 - Z.zero k))⁻¹‖ ≤
        2 / (1 + Complex.normSq (Z.gamma k)) := by
  let D := Z.zero k * (1 - Z.zero k)
  have hg : 4 ≤ ‖Z.gamma k‖ ^ 2 := by nlinarith [norm_nonneg (Z.gamma k)]
  have hd : ‖Z.gamma k‖ ^ 2 ≤ ‖D‖ + 1 / 4 := by
    calc
      _ = ‖(Z.gamma k) ^ 2‖ := (norm_pow _ _).symm
      _ = ‖D - 1 / 4‖ := by rw [show D = _ from gamma_product Z k]; congr 1; ring
      _ ≤ ‖D‖ + ‖(1 / 4 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by norm_num
  have hDp : 0 < ‖D‖ := by linarith
  change ‖D⁻¹‖ ≤ _ ∧ ‖D⁻¹‖ ≤ _
  rw [norm_inv, inv_eq_one_div]
  constructor
  · apply (div_le_iff₀ hDp).mpr
    nlinarith
  · rw [div_le_div_iff₀ hDp (by positivity), Complex.normSq_eq_norm_sq]
    nlinarith

private theorem collapsed_kernel_bound (x z : ℂ) (hx : ‖x‖ ≤ 1 / 2)
    (hz : ‖z‖ ≤ 1 / 4) :
    (1 - z) ^ 2 + x * z ≠ 0 ∧
      ‖x * (1 + z) / ((1 - z) * ((1 - z) ^ 2 + x * z))‖ ≤ 4 * ‖x‖ := by
  have ha : 3 / 4 ≤ ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    norm_num at h
    linarith
  have hb : ‖1 + z‖ ≤ 5 / 4 := by
    exact (norm_add_le _ _).trans (by simpa using (by linarith : 1 + ‖z‖ ≤ 5 / 4))
  have hc : ‖x‖ * ‖z‖ ≤ 1 / 8 := by
    calc
      _ ≤ (1 / 2 : ℝ) * (1 / 4) := mul_le_mul hx hz (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hd : 7 / 16 ≤ ‖(1 - z) ^ 2 + x * z‖ := by
    have h := norm_sub_norm_le ((1 - z) ^ 2) (-(x * z))
    rw [sub_neg_eq_add, norm_neg, norm_pow, norm_mul] at h
    nlinarith [norm_nonneg (1 - z)]
  have hd0 : (1 - z) ^ 2 + x * z ≠ 0 := norm_pos_iff.mp (by linarith)
  refine ⟨hd0, ?_⟩
  have hden : 21 / 64 ≤ ‖1 - z‖ * ‖(1 - z) ^ 2 + x * z‖ := by
    have h := mul_le_mul ha hd (by norm_num : (0 : ℝ) ≤ 7 / 16) (norm_nonneg _)
    norm_num at h
    exact h
  rw [norm_div, norm_mul, norm_mul]
  calc
    _ ≤ (‖x‖ * (5 / 4)) / (‖1 - z‖ * ‖(1 - z) ^ 2 + x * z‖) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
        (by positivity)
    _ ≤ (‖x‖ * (5 / 4)) / (21 / 64) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ 4 * ‖x‖ := by nlinarith [norm_nonneg x]

private theorem kernel_tail_bound (Z : ZeroData) (k : ℕ) (hk : 2 ≤ ‖Z.gamma k‖)
    (z : ℂ) (hz : ‖z‖ ≤ 1 / 4) :
    ‖reflectedLiKernel Z k z‖ ≤ 4 * ((Z.multiplicity k : ℝ) /
      (1 + Complex.normSq (Z.gamma k))) := by
  let x := (Z.zero k * (1 - Z.zero k))⁻¹
  have hx := inverse_product_bound Z k hk
  have hbound := collapsed_kernel_bound x z hx.1 hz
  have hrel := ratio_relations (Z.zero k) (zero_ne Z k).1 (zero_ne Z k).2
  have hz0 : 1 - z ≠ 0 := by
    intro he
    have he' : z = 1 := (sub_eq_zero.mp he).symm
    simp [he'] at hz
  rw [reflectedLiKernel, kernel_collapse _ _ x z hrel.1 hrel.2 hz0 hbound.1,
    norm_mul, norm_div, Complex.norm_natCast]
  norm_num only [norm_ofNat]
  calc
    _ ≤ ((Z.multiplicity k : ℝ) / 2) * (4 * ‖x‖) :=
      mul_le_mul_of_nonneg_left hbound.2 (by positivity)
    _ ≤ ((Z.multiplicity k : ℝ) / 2) *
        (4 * (2 / (1 + Complex.normSq (Z.gamma k)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2 (by norm_num))
        (by positivity)
    _ = _ := by ring

private theorem reciprocal_weight_summable (Z : ZeroData) :
    Summable (fun k : ℕ =>
      (Z.multiplicity k : ℝ) / (1 + Complex.normSq (Z.gamma k))) := by
  have h := (zeroEquiv Z).summable_iff.mpr (Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam)
  refine h.congr fun k => ?_
  change (Zeta23.zeroMult (Z.zero k) : ℝ) /
    (1 + Complex.normSq (Zeta23.gammaOf (Z.zero k))) = _
  rw [← multiplicity_eq_zeroMult, gammaOf_eq_spectralParameter]
  rfl

/-- The reflection-paired Li kernels have an explicit summable tail on the
closed quarter disk, hence absolute pointwise and uniform unordered convergence.
No critical-line or zero-height lower-bound hypothesis is required. -/
theorem reflected_li_kernel_normal_convergence (Z : ZeroData) :
    (∀ k : ℕ, 2 ≤ ‖Z.gamma k‖ → ∀ z : ℂ, ‖z‖ ≤ 1 / 4 →
      ‖reflectedLiKernel Z k z‖ ≤ 4 * ((Z.multiplicity k : ℝ) /
        (1 + Complex.normSq (Z.gamma k)))) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 / 4 → Summable (fun k : ℕ => ‖reflectedLiKernel Z k z‖)) ∧
    TendstoUniformlyOn
      (fun A : Finset ℕ => fun z : ℂ => ∑ k ∈ A, reflectedLiKernel Z k z)
      (fun z : ℂ => ∑' k : ℕ, reflectedLiKernel Z k z) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  classical
  have hw := (reciprocal_weight_summable Z).mul_left 4
  have he : ∀ᶠ k in cofinite, ∀ z : ℂ, ‖z‖ ≤ 1 / 4 →
      ‖reflectedLiKernel Z k z‖ ≤ 4 * ((Z.multiplicity k : ℝ) /
        (1 + Complex.normSq (Z.gamma k))) := by
    filter_upwards [(Z.symmetricIndices 2).finite_toSet.compl_mem_cofinite] with k hk z hz
    have hk' : 2 < ‖Z.gamma k‖ := by simpa using hk
    exact kernel_tail_bound Z k hk'.le z hz
  refine ⟨kernel_tail_bound Z, ?_, ?_⟩
  · intro z hz
    apply Summable.of_norm_bounded_eventually hw
    filter_upwards [he] with k hk
    simpa only [norm_norm] using hk z hz
  · apply tendstoUniformlyOn_tsum_of_cofinite_eventually hw
    filter_upwards [he] with k hk z hz
    exact hk z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)

#print axioms reflected_li_kernel_normal_convergence

end D5.S3.Weil.ZeroData.LiReflectedKernel
