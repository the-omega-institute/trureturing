/- GID: D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Smoothing
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Smoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids WeightedStieltjes analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/WeightedStieltjes.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Contour

/-! Original WeightedStieltjes analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.WeightedStieltjes

open Complex Finset Filter MeasureTheory Set Asymptotics Topology
open scoped Real Topology Interval

/-- **High-Frequency Norm Bound for `smoothedZeroTerm` (`ρ.re = 1 / 2`)**:
If `0 < x`, `0 < h`, `ρ.re = 1 / 2`, and `ρ.im ≠ 0`, then
$$\|\text{smoothedZeroTerm}(x, h, \rho)\| \le \frac{2 (x + h)^{3/2}}{h |\rho.\text{im}|^2}.$$ -/
theorem norm_smoothedZeroTerm_le_two_mul_rpow_div_sq_im {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ‖smoothedZeroTerm x h ρ‖ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) / (h * |ρ.im| ^ 2) := by
  unfold smoothedZeroTerm
  rw [norm_div, mul_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]
  have hre1 : (ρ + 1).re = 3 / 2 := by
    simp [hre]
    norm_num
  have hxh_pos : 0 < x + h := by linarith
  have hnum : ‖((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)‖ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) := by
    calc
      ‖((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)‖
        ≤ ‖((x + h : ℝ) : ℂ) ^ (ρ + 1)‖ + ‖(x : ℂ) ^ (ρ + 1)‖ := norm_sub_le _ _
      _ = (x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxh_pos,
          Complex.norm_cpow_eq_rpow_re_of_pos hx, hre1]
      _ ≤ (x + h) ^ (3 / 2 : ℝ) + (x + h) ^ (3 / 2 : ℝ) := by
        gcongr
        linarith
      _ = 2 * (x + h) ^ (3 / 2 : ℝ) := by ring
  have hden : h * |ρ.im| ^ 2 ≤ h * ‖ρ * (ρ + 1)‖ :=
    mul_le_mul_of_nonneg_left (sq_abs_im_le_norm_mul_add_one ρ) hh.le
  have hden_pos : 0 < h * |ρ.im| ^ 2 := by
    have : 0 < |ρ.im| := abs_pos.mpr him
    positivity
  calc
    ‖((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)‖ / (h * ‖ρ * (ρ + 1)‖)
      ≤ (2 * (x + h) ^ (3 / 2 : ℝ)) / (h * ‖ρ * (ρ + 1)‖) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (2 * (x + h) ^ (3 / 2 : ℝ)) / (h * |ρ.im| ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hden_pos hden

/-- **Exact Difference Quotient of a Nontrivial Zero Residue `resZeroRho`**:
`(resZeroRho (x₁ + h) ρ - resZeroRho x₁ ρ) / (h : ℂ) = -(analyticOrderNatAt riemannZeta ρ : ℂ) *
smoothedZeroTerm x₁ h ρ`. -/
theorem resZeroRho_add_sub_div (x₁ h : ℝ) (ρ : ℂ) :
    (resZeroRho (x₁ + h) ρ - resZeroRho x₁ ρ) / (h : ℂ) =
      -(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ := by
  unfold resZeroRho smoothedPerronKernel smoothedZeroTerm
  rw [← mul_sub, mul_div_assoc, ← sub_div, div_div,
    show ρ * (ρ + 1) * (h : ℂ) = (h : ℂ) * ρ * (ρ + 1) by ring]

/-- **Exact Difference Quotient of the Finite Zero-Residue Sum**:
For any `S : Finset ℂ`,
`(∑ ρ ∈ S, resZeroRho (x₁ + h) ρ - ∑ ρ ∈ S, resZeroRho x₁ ρ) / (h : ℂ) = -(∑ ρ ∈ S,
(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ)`. -/
theorem sum_resZeroRho_add_sub_div (x₁ h : ℝ) (S : Finset ℂ) :
    (∑ ρ ∈ S, resZeroRho (x₁ + h) ρ - ∑ ρ ∈ S, resZeroRho x₁ ρ) / (h : ℂ) =
      -(∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ) := by
  rw [← sum_sub_distrib, sum_div, ← sum_neg_distrib]
  refine sum_congr rfl fun ρ _ ↦ ?_
  rw [resZeroRho_add_sub_div, neg_mul]

/-- Real-part version of `sum_resZeroRho_add_sub_div`. -/
theorem re_sum_resZeroRho_add_sub_div (x₁ h : ℝ) (S : Finset ℂ) :
    ((∑ ρ ∈ S, resZeroRho (x₁ + h) ρ).re - (∑ ρ ∈ S, resZeroRho x₁ ρ).re) / h =
      (-(∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ)).re := by
  rw [← sub_re, ← Complex.div_ofReal_re, sum_resZeroRho_add_sub_div]

/-- **Low/High Frequency Partition of `nontrivialZetaZerosUpTo U`**:
For `T ≤ U` and any function `f`, the sum over `nontrivialZetaZerosUpTo U` splits into the sum
over `nontrivialZetaZerosUpTo T` plus the sum over `nontrivialZetaZerosBetween T U`. -/
theorem sum_nontrivialZetaZerosUpTo_eq_add_between {α : Type*} [AddCommMonoid α]
    {T U : ℝ} (hTU : T ≤ U) (f : ℂ → α) :
    ∑ ρ ∈ nontrivialZetaZerosUpTo U, f ρ =
      (∑ ρ ∈ nontrivialZetaZerosUpTo T, f ρ) +
        ∑ ρ ∈ nontrivialZetaZerosBetween T U, f ρ := by
  rw [← filter_not_lt_abs_im_nontrivialZetaZerosUpTo hTU, nontrivialZetaZerosBetween,
    add_comm, sum_filter_add_sum_filter_not]

/-- **Low-Frequency Zero-Sum Bound (`|ρ.im| ≤ T`) under `RiemannHypothesis`**:
For `0 < x₁` and `0 < h`,
$$\left\|\sum_{\rho \in \mathcal{Z}(T)} (m_\rho : \mathbb{C}) \cdot \text{smoothedZeroTerm}(x_1, h,
\rho)\right\|
  \le \sqrt{x_1 + h} \sum_{\rho \in \mathcal{Z}(T)} \frac{m_\rho}{\|\rho\|}.$$ -/
theorem norm_sum_smoothedZeroTerm_upTo_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x₁ h T : ℝ} (hx₁ : 0 < x₁) (hh : 0 < h) :
    ‖∑ ρ ∈ nontrivialZetaZerosUpTo T,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ‖ ≤
      Real.sqrt (x₁ + h) *
        ∑ ρ ∈ nontrivialZetaZerosUpTo T, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ρ hρ ↦ ?_)
  have hρ_zero : IsNontrivialZetaZero ρ := (mem_nontrivialZetaZerosUpTo.mp hρ).1
  have hre : ρ.re = 1 / 2 := hRH ρ hρ_zero.1 hρ_zero.2.1 hρ_zero.2.2
  rw [norm_mul, Complex.norm_natCast]
  calc
    (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖smoothedZeroTerm x₁ h ρ‖
      ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (Real.sqrt (x₁ + h) / ‖ρ‖) :=
        mul_le_mul_of_nonneg_left (norm_smoothedZeroTerm_le_sqrt_div_norm hx₁ hh hre)
          (Nat.cast_nonneg _)
    _ = Real.sqrt (x₁ + h) * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by ring

/-- **High-Frequency Zero-Sum Bound (`T < |ρ.im| ≤ U`) under `RiemannHypothesis`**:
For `0 < x₁`, `0 < h`, and `0 < T`,
$$\left\|\sum_{\rho \in \mathcal{Z}(T, U)} (m_\rho : \mathbb{C}) \cdot \text{smoothedZeroTerm}(x_1,
h, \rho)\right\|
  \le \frac{2 (x_1 + h)^{3/2}}{h} \sum_{\rho \in \mathcal{Z}(T, U)}
  \frac{m_\rho}{|\rho.\text{im}|^2}.$$ -/
theorem norm_sum_smoothedZeroTerm_between_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x₁ h T U : ℝ} (hx₁ : 0 < x₁) (hh : 0 < h) (hT : 0 < T) :
    ‖∑ ρ ∈ nontrivialZetaZerosBetween T U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ‖ ≤
      (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
        ∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2 := by
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ρ hρ ↦ ?_)
  obtain ⟨hρ_zero, _, hρ_gt⟩ := mem_nontrivialZetaZerosBetween.mp hρ
  have hre : ρ.re = 1 / 2 := hRH ρ hρ_zero.1 hρ_zero.2.1 hρ_zero.2.2
  have him : ρ.im ≠ 0 := abs_pos.mp (hT.trans hρ_gt)
  rw [norm_mul, Complex.norm_natCast]
  calc
    (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖smoothedZeroTerm x₁ h ρ‖
      ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) *
          (2 * (x₁ + h) ^ (3 / 2 : ℝ) / (h * |ρ.im| ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (norm_smoothedZeroTerm_le_two_mul_rpow_div_sq_im hx₁ hh hre him) (Nat.cast_nonneg _)
    _ = (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) := by ring

/-- **Combined Low/High Frequency Zero-Sum Bound up to `U` under `RiemannHypothesis`**:
For `0 < x₁`, `0 < h`, `0 < T`, and `T ≤ U`, splitting at `T` bounds the full zero sum up to `U`. -/
theorem norm_sum_smoothedZeroTerm_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x₁ h T U : ℝ}
    (hx₁ : 0 < x₁) (hh : 0 < h) (hT : 0 < T) (hTU : T ≤ U) :
    ‖∑ ρ ∈ nontrivialZetaZerosUpTo U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ‖ ≤
      Real.sqrt (x₁ + h) *
        (∑ ρ ∈ nontrivialZetaZerosUpTo T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
      (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
        (∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) := by
  rw [sum_nontrivialZetaZerosUpTo_eq_add_between hTU]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_sum_smoothedZeroTerm_upTo_le_of_riemannHypothesis hRH hx₁ hh)
    (norm_sum_smoothedZeroTerm_between_le_of_riemannHypothesis hRH hx₁ hh hT))

/-- The contour-shift boundary integral error at `y` along the shifted vertical line `Re s = a`
and the top/bottom horizontal segments `[a, 2] ± i U`. -/
noncomputable def contourBoundaryError (y a U : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand y (a + (t : ℂ) * I)‖ +
    (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ + (U : ℂ) * I)‖ +
    (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ - (U : ℂ) * I)‖

/-- The combined difference-quotient contour and vertical-tail error for `|ψ(x) - x|` over
`[x - h, x]` and `[x, x + h]`, bounding the vertical tail by `4 * (x + h) ^ 3 / (Real.pi * h * U)`
and the horizontal-segment and left-vertical-line terms at `x - h, x, x + h`. -/
noncomputable def contourDiffError (x h a U : ℝ) : ℝ :=
  4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
    max ((contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h)
      ((contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h)

/-- Exact contour remainder at `y` before taking norms of the main term, `s = 0` pole, or zeros. -/
noncomputable def psi1ContourRemainder (y U : ℝ) : ℝ :=
  psi1 y - y ^ 2 / 2 + y * Real.log (2 * Real.pi) -
    (∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho y ρ).re

/-- Bound on `|psi1ContourRemainder y U|` for `1 ≤ y`, `0 < U`, `-1 / 2 < a < 0`. -/
theorem abs_psi1ContourRemainder_le_of_neg
    {y U a : ℝ} (hy : 1 ≤ y) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |psi1ContourRemainder y U| ≤
      2 * y ^ (3 : ℝ) / (Real.pi * U) + contourBoundaryError y a U := by
  unfold psi1ContourRemainder contourBoundaryError
  rw [sum_resZeroRho_eq]
  exact abs_psi1_sub_main_add_log_two_pi_sub_zeroSum_le_of_neg hy hU ha ha_neg h_no_horiz

/-- **Exact Difference Quotient Decomposition of `(psi1 (x₁ + h) - psi1 x₁) / h`**:
For `h ≠ 0`,
$$\frac{\psi_1(x_1 + h) - \psi_1(x_1)}{h} - \left(x_1 + \frac{h}{2}\right)
  = -\log(2\pi)
    + \left(-\sum_{\rho \in \mathcal{Z}(U)} (m_\rho : \mathbb{C}) \cdot
    \text{smoothedZeroTerm}(x_1, h, \rho)\right).\text{re}
    + \frac{\text{psi1ContourRemainder}(x_1 + h, U) - \text{psi1ContourRemainder}(x_1, U)}{h}.$$ -/
theorem psi1_add_sub_div_sub_linear_eq {x₁ h U : ℝ} (hh : h ≠ 0) :
    (psi1 (x₁ + h) - psi1 x₁) / h - (x₁ + h / 2) =
      -Real.log (2 * Real.pi) +
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ)).re +
        (psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U) / h := by
  have h_zero := re_sum_resZeroRho_add_sub_div x₁ h (nontrivialZetaZerosUpTo U)
  unfold psi1ContourRemainder
  rw [← h_zero]
  field_simp [hh]
  ring

/-- **Difference Quotient Error Bound on `[x₁, x₁ + h]` (`1 ≤ x₁`, `0 < h`) under
`RiemannHypothesis`**:
Taking the difference quotient before taking norms bounds
`|(psi1 (x₁ + h) - psi1 x₁) / h - (x₁ + h / 2)|` by `Real.log (2 * Real.pi)` plus the low/high
frequency zero sums and the contour difference error. -/
theorem abs_psi1_add_sub_div_sub_linear_le_of_neg
    (hRH : RiemannHypothesis) {x₁ h T U a : ℝ}
    (hx₁ : 1 ≤ x₁) (hh : 0 < h) (hT : 0 < T) (hTU : T ≤ U)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |(psi1 (x₁ + h) - psi1 x₁) / h - (x₁ + h / 2)| ≤
      Real.log (2 * Real.pi) +
        Real.sqrt (x₁ + h) *
          (∑ ρ ∈ nontrivialZetaZerosUpTo T,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
        (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
          (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) +
        (4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * h * U) +
          (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) / h) := by
  have hU : 0 < U := hT.trans_le hTU
  have hx₁_pos : 0 < x₁ := zero_lt_one.trans_le hx₁
  have hx₂ : 1 ≤ x₁ + h := by linarith
  rw [psi1_add_sub_div_sub_linear_eq hh.ne']
  set Z : ℂ := ∑ ρ ∈ nontrivialZetaZerosUpTo U,
    (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ
  set R_diff : ℝ := (psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U) / h
  have htri : |-Real.log (2 * Real.pi) + (-Z).re + R_diff| ≤
      |-Real.log (2 * Real.pi)| + |(-Z).re| + |R_diff| := by
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hpi : 1 ≤ Real.pi := Real.two_le_pi.trans' one_le_two
  have hlog_pos : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have h1 : |-Real.log (2 * Real.pi)| = Real.log (2 * Real.pi) := by
    rw [abs_neg, abs_of_nonneg hlog_pos]
  have h2 : |(-Z).re| ≤
      Real.sqrt (x₁ + h) *
        (∑ ρ ∈ nontrivialZetaZerosUpTo T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
      (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
        (∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) := by
    calc
      |(-Z).re| ≤ ‖-Z‖ := Complex.abs_re_le_norm (-Z)
      _ = ‖Z‖ := norm_neg Z
      _ ≤ _ := norm_sum_smoothedZeroTerm_le_of_riemannHypothesis hRH hx₁_pos hh hT hTU
  have hR₁ := abs_psi1ContourRemainder_le_of_neg hx₁ hU ha ha_neg h_no_horiz
  have hR₂ := abs_psi1ContourRemainder_le_of_neg hx₂ hU ha ha_neg h_no_horiz
  have hrpow_le : x₁ ^ (3 : ℝ) ≤ (x₁ + h) ^ (3 : ℝ) :=
    Real.rpow_le_rpow hx₁_pos.le (by linarith) (by norm_num)
  have htail_le : 2 * x₁ ^ (3 : ℝ) / (Real.pi * U) ≤ 2 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) := by
    gcongr
  have h3 : |R_diff| ≤
      4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * h * U) +
        (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) / h := by
    dsimp [R_diff]
    rw [abs_div, abs_of_pos hh]
    have hsub : |psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U| ≤
        |psi1ContourRemainder (x₁ + h) U| + |psi1ContourRemainder x₁ U| := abs_sub _ _
    have h4 : 2 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) + 2 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) =
        4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) := by ring
    have hsum : |psi1ContourRemainder (x₁ + h) U| + |psi1ContourRemainder x₁ U| ≤
        4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) +
          (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) := by
      linarith
    calc
      |psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U| / h
        ≤ (4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) +
            (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U)) / h :=
          div_le_div_of_nonneg_right (hsub.trans hsum) hh.le
      _ = 4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * h * U) +
            (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) / h := by
          rw [add_div, div_div]
          ring
  linarith

/-- **Difference Quotient Contour Shift & Low/High Frequency Split Theorem**:
Combining the forward difference quotient on `[x, x + h]` and the backward difference quotient on
`[x - h, x]` (`1 ≤ x - h`, `0 < h`) with the monotonicity sandwich for `ψ` and the low/high
frequency zero split at cutoff `T` (`0 < T ≤ U`) proves:
$$|\psi(x) - x| \le \frac{h}{2} + \log(2\pi)
  + \sqrt{x + h} \sum_{\rho \in \mathcal{Z}(T)} \frac{m_\rho}{\|\rho\|}
  + \frac{2 (x + h)^{3/2}}{h} \sum_{\rho \in \mathcal{Z}(T, U)} \frac{m_\rho}{|\rho.\text{im}|^2}
  + \text{contourDiffError}(x, h, a, U).$$ -/
theorem abs_psi_sub_self_le_smoothed_contour_shift
    (hRH : RiemannHypothesis) {x h T U a : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hT : 0 < T) (hTU : T ≤ U)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (∑ ρ ∈ nontrivialZetaZerosUpTo T,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) +
        contourDiffError x h a U := by
  have hx : 1 ≤ x := by linarith
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have hU : 0 < U := hT.trans_le hTU
  set S_low : ℝ := ∑ ρ ∈ nontrivialZetaZerosUpTo T,
    (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖
  set S_high : ℝ := ∑ ρ ∈ nontrivialZetaZerosBetween T U,
    (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2
  have hS_low_nonneg : 0 ≤ S_low :=
    sum_nonneg fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hS_high_nonneg : 0 ≤ S_high :=
    sum_nonneg fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · -- Forward difference on `[x, x + h]`: bounds `Chebyshev.psi x - x`
    have h_sand := psi_le_psi1_add_sub_div x hh
    have h_fwd := abs_psi1_add_sub_div_sub_linear_le_of_neg hRH hx hh hT hTU ha ha_neg h_no_horiz
    have h_fwd_upper : (psi1 (x + h) - psi1 x) / h - (x + h / 2) ≤
        Real.log (2 * Real.pi) + Real.sqrt (x + h) * S_low +
          (2 * (x + h) ^ (3 / 2 : ℝ) / h) * S_high +
          (4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
            (contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h) :=
      (le_abs_self _).trans h_fwd
    have h_max : (contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h ≤
        max ((contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h)
          ((contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h) :=
      le_max_left _ _
    unfold contourDiffError
    linarith
  · -- Backward difference on `[x - h, x]`: bounds `x - Chebyshev.psi x`
    have h_sand := psi1_sub_psi1_sub_div_le_psi x hh
    have h_bwd :=
      abs_psi1_add_sub_div_sub_linear_le_of_neg hRH hx_sub hh hT hTU ha ha_neg h_no_horiz
    have hx_add : x - h + h = x := sub_add_cancel x h
    rw [hx_add] at h_bwd
    have h_bwd_lower : -(Real.log (2 * Real.pi) + Real.sqrt x * S_low +
          (2 * x ^ (3 / 2 : ℝ) / h) * S_high +
          (4 * x ^ (3 : ℝ) / (Real.pi * h * U) +
            (contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h)) ≤
        (psi1 x - psi1 (x - h)) / h - (x - h + h / 2) :=
      neg_le_of_abs_le h_bwd
    have h_sqrt_le : Real.sqrt x * S_low ≤ Real.sqrt (x + h) * S_low :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hS_low_nonneg
    have h_rpow32_le : (2 * x ^ (3 / 2 : ℝ) / h) * S_high ≤
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) * S_high := by
      gcongr
      linarith
    have h_rpow3_le : 4 * x ^ (3 : ℝ) / (Real.pi * h * U) ≤
        4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) := by
      gcongr
      linarith
    have h_max : (contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h ≤
        max ((contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h)
          ((contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h) :=
      le_max_right _ _
    unfold contourDiffError
    linarith

/-!
## Section 1: Fourth-Order Euler–Maclaurin Identity & Low-Lying Zero-Free Region `|ρ.im| > 6`
-/

/-!
## Section 5: Multiplicity-Weighted Stieltjes Bounds (`weightedZeroCountingFunction`) & Asymptotic
Limit `U → ∞`
-/

/-- Under `RiemannHypothesis`, `weightedZeroCountingFunction 6 = 0`. -/
theorem weightedZeroCountingFunction_six_eq_zero (hRH : RiemannHypothesis) :
    weightedZeroCountingFunction 6 = 0 :=
  weightedZeroCountingFunction_eq_zero_of_le_six hRH le_rfl

/-- Whenever `weightedZeroCountingFunction t₀ = 0`, `nontrivialZetaZerosUpTo t₀ = ∅`. -/
theorem nontrivialZetaZerosUpTo_eq_empty_of_weightedZeroCountingFunction_eq_zero
    {t₀ : ℝ} (h0 : weightedZeroCountingFunction t₀ = 0) :
    nontrivialZetaZerosUpTo t₀ = ∅ := by
  unfold weightedZeroCountingFunction at h0
  rw [Finset.sum_eq_zero_iff] at h0
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ρ hρ
  have h1 := one_le_analyticOrderNatAt_of_isNontrivialZetaZero
    (mem_nontrivialZetaZerosUpTo.mp hρ).1
  have h_zero := h0 ρ hρ
  omega

/-- Whenever `weightedZeroCountingFunction t₀ = 0`, `nontrivialZetaZerosUpTo T` coincides with
`nontrivialZetaZerosBetween t₀ T`. -/
theorem nontrivialZetaZerosUpTo_eq_between_of_weightedZeroCountingFunction_eq_zero
    {t₀ T : ℝ} (h0 : weightedZeroCountingFunction t₀ = 0) :
    nontrivialZetaZerosUpTo T = nontrivialZetaZerosBetween t₀ T := by
  have hempty := nontrivialZetaZerosUpTo_eq_empty_of_weightedZeroCountingFunction_eq_zero h0
  ext ρ
  simp only [mem_nontrivialZetaZerosUpTo, mem_nontrivialZetaZerosBetween]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2, ?_⟩, fun ⟨h1, h2, _⟩ ↦ ⟨h1, h2⟩⟩
  by_contra! hle
  have hmem : ρ ∈ nontrivialZetaZerosUpTo t₀ := mem_nontrivialZetaZerosUpTo.mpr ⟨h1, hle⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty ρ hmem

/-- For `T ≤ U`, the multiplicity sum over `nontrivialZetaZerosBetween T U` plus
`weightedZeroCountingFunction T` equals `weightedZeroCountingFunction U`. -/
theorem sum_weighted_nontrivialZetaZerosBetween_add_eq {T U : ℝ} (hTU : T ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U, analyticOrderNatAt riemannZeta ρ) +
      weightedZeroCountingFunction T =
      weightedZeroCountingFunction U := by
  unfold nontrivialZetaZerosBetween weightedZeroCountingFunction
  rw [← filter_not_lt_abs_im_nontrivialZetaZerosUpTo hTU]
  exact sum_filter_add_sum_filter_not (nontrivialZetaZerosUpTo U) (fun ρ : ℂ ↦ T < |ρ.im|) _

/-- Real-cast version of `sum_weighted_nontrivialZetaZerosBetween_add_eq`. -/
theorem sum_weighted_nontrivialZetaZerosBetween_real {T U : ℝ} (hTU : T ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
      (weightedZeroCountingFunction U : ℝ) - (weightedZeroCountingFunction T : ℝ) := by
  have h :
      (∑ ρ ∈ nontrivialZetaZerosBetween T U, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
        (weightedZeroCountingFunction T : ℝ) =
        (weightedZeroCountingFunction U : ℝ) := by
    exact_mod_cast sum_weighted_nontrivialZetaZerosBetween_add_eq hTU
  linarith

/-- For `T ≤ t ≤ U`, the multiplicity-weighted indicator sum equals
`(weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)`. -/
theorem sum_ite_abs_im_le_weighted_nontrivialZetaZerosBetween {T t U : ℝ}
    (hTt : T ≤ t) (htU : t ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      if |ρ.im| ≤ t then (analyticOrderNatAt riemannZeta ρ : ℝ) else 0) =
      (weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ) := by
  rw [← sum_filter, filter_abs_im_le_nontrivialZetaZerosBetween htU,
    sum_weighted_nontrivialZetaZerosBetween_real hTt]

/-- Pointwise decomposition of
`((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t`
on `Set.Ioc T U` as a finite sum of weighted indicator functions over `nontrivialZetaZerosBetween T
U`. -/
theorem eqOn_sub_weightedZeroCountingFunction_mul_sum_indicator {T U : ℝ} (g' : ℝ → ℝ) :
    Set.EqOn
      (fun t : ℝ ↦
        ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t)
      (fun t : ℝ ↦
        ∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (Set.Ici |ρ.im|).indicator g' t)
      (Set.Ioc T U) := by
  intro t ht
  dsimp only
  rw [← sum_ite_abs_im_le_weighted_nontrivialZetaZerosBetween ht.1.le ht.2, sum_mul]
  refine sum_congr rfl fun ρ _ ↦ ?_
  simp only [Set.indicator, Set.mem_Ici]
  split_ifs <;> ring

/-- If `g'` is continuous on `Set.Icc T U` (`T ≤ U`), then
`fun t ↦ (weightedZeroCountingFunction t : ℝ) * g' t` is `IntervalIntegrable` on `T..U`. -/
theorem intervalIntegrable_weightedZeroCountingFunction_mul {T U : ℝ} (hTU : T ≤ U)
    {g' : ℝ → ℝ} (hcont : ContinuousOn g' (Set.Icc T U)) :
    IntervalIntegrable
      (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * g' t) volume T U := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTU]
  have h_sub_int :
      IntegrableOn
        (fun t : ℝ ↦
          ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t)
        (Set.Ioc T U) := by
    refine IntegrableOn.congr_fun ?_
      (eqOn_sub_weightedZeroCountingFunction_mul_sum_indicator g').symm measurableSet_Ioc
    exact integrable_finsetSum (nontrivialZetaZerosBetween T U) fun ρ hρ ↦
      (integrableOn_indicator_of_continuousOn
        (mem_nontrivialZetaZerosBetween.mp hρ).2.2 hcont).const_mul _
  have h_const_int :
      IntegrableOn (fun t : ℝ ↦ (weightedZeroCountingFunction T : ℝ) * g' t) (Set.Ioc T U) :=
    (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _
  have h_add := h_sub_int.add h_const_int
  refine h_add.congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
  simp only [Pi.add_apply]
  ring

/-- **Multiplicity-Weighted Stieltjes Integration-by-Parts Identity**:
For any `T ≤ U` and any `g, g' : ℝ → ℝ` with `HasDerivAt g (g' t) t` on `Set.Icc T U` and
`ContinuousOn g' (Set.Icc T U)`,
$$\sum_{\rho \in \mathcal{Z}(T, U)} m_\rho \, g(|\operatorname{Im} \rho|)
  = N_{\text{mult}}(U) g(U) - N_{\text{mult}}(T) g(T) - \int_T^U N_{\text{mult}}(t) g'(t) \, dt.$$
-/
theorem sum_weighted_nontrivialZetaZerosBetween_eq_stieltjes {T U : ℝ} (hTU : T ≤ U)
    {g g' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc T U, HasDerivAt g (g' t) t)
    (hcont : ContinuousOn g' (Set.Icc T U)) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im|) =
      (weightedZeroCountingFunction U : ℝ) * g U -
        (weightedZeroCountingFunction T : ℝ) * g T -
        ∫ t in T..U, (weightedZeroCountingFunction t : ℝ) * g' t := by
  have h_ind_int :
      (∫ t in Set.Ioc T U,
          ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t) =
        ((weightedZeroCountingFunction U : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g U -
          ∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im| := by
    rw [setIntegral_congr_fun measurableSet_Ioc
        (eqOn_sub_weightedZeroCountingFunction_mul_sum_indicator g'),
      integral_finsetSum (nontrivialZetaZerosBetween T U) fun ρ hρ ↦
        (integrableOn_indicator_of_continuousOn
          (mem_nontrivialZetaZerosBetween.mp hρ).2.2 hcont).const_mul _]
    calc
      (∑ ρ ∈ nontrivialZetaZerosBetween T U,
          ∫ t in Set.Ioc T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * (Set.Ici |ρ.im|).indicator g' t)
        = ∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * (g U - g |ρ.im|) := by
          refine sum_congr rfl fun ρ hρ ↦ ?_
          rw [integral_const_mul, setIntegral_indicator_deriv_eq_sub
            (mem_nontrivialZetaZerosBetween.mp hρ).2.2
            (mem_nontrivialZetaZerosBetween.mp hρ).2.1 hderiv hcont]
      _ = (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * g U) -
          ∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im| := by
          rw [← sum_sub_distrib]
          refine sum_congr rfl fun ρ _ ↦ by ring
      _ = ((weightedZeroCountingFunction U : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g U -
            ∑ ρ ∈ nontrivialZetaZerosBetween T U,
              (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im| := by
          rw [← sum_mul, sum_weighted_nontrivialZetaZerosBetween_real hTU]
  have h_ftc : (∫ t in T..U, g' t) = g U - g T := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · intro t ht
      rw [Set.uIcc_of_le hTU] at ht
      exact hderiv t ht
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
      exact hcont.integrableOn_Icc
  have h_int_g' : IntervalIntegrable g' volume T U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
    exact hcont.integrableOn_Icc
  have h_int_N :
      IntervalIntegrable
        (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * g' t) volume T U :=
    intervalIntegrable_weightedZeroCountingFunction_mul hTU hcont
  have h_split :
      (∫ t in Set.Ioc T U,
          ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t) =
        (∫ t in T..U, (weightedZeroCountingFunction t : ℝ) * g' t) -
          (weightedZeroCountingFunction T : ℝ) * (g U - g T) := by
    rw [← intervalIntegral.integral_of_le hTU]
    have h_sub_fn :
        (fun t : ℝ ↦
            ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t) =
          fun t : ℝ ↦
            (weightedZeroCountingFunction t : ℝ) * g' t -
              (weightedZeroCountingFunction T : ℝ) * g' t := by
      ext t; ring
    rw [h_sub_fn, intervalIntegral.integral_sub h_int_N (h_int_g'.const_mul _),
      intervalIntegral.integral_const_mul, h_ftc]
  linarith

/-- Derivative of `1 / t ^ 2` at `t ≠ 0` is `-2 / t ^ 3`. -/
theorem hasDerivAt_one_div_sq {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 1 / x ^ 2) (-2 / t ^ 3) t := by
  have hd : HasDerivAt (fun x : ℝ ↦ (x ^ 2)⁻¹) (-(2 * t ^ (2 - 1)) / (t ^ 2) ^ 2) t :=
    (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)
  simp only [one_div]
  refine hd.congr_deriv ?_
  field_simp [ht]
  ring

/-- **Multiplicity-Weighted Stieltjes Identity for $\sum_{t_0 < |\gamma| \le T}
\frac{m_\rho}{|\gamma|}$**:
For `0 < t₀ ≤ T`,
$$\sum_{\rho \in \mathcal{Z}(t_0, T)} \frac{m_\rho}{|\operatorname{Im} \rho|}
  = \frac{N_{\text{mult}}(T)}{T} - \frac{N_{\text{mult}}(t_0)}{t_0}
    + \int_{t_0}^T \frac{N_{\text{mult}}(t)}{t^2} \, dt.$$ -/
theorem sum_weighted_inv_abs_im_nontrivialZetaZerosBetween_eq
    {t₀ T : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    (∑ ρ ∈ nontrivialZetaZerosBetween t₀ T,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im|) =
      (weightedZeroCountingFunction T : ℝ) / T -
        (weightedZeroCountingFunction t₀ : ℝ) / t₀ +
        ∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2 := by
  have hderiv : ∀ t ∈ Set.Icc t₀ T, HasDerivAt (fun x : ℝ ↦ 1 / x) (-1 / t ^ 2) t :=
    fun t ht ↦ hasDerivAt_one_div (ht₀.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ ↦ -1 / t ^ 2) (Set.Icc t₀ T) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht_pos.ne')
  have h_eq :
      (∑ ρ ∈ nontrivialZetaZerosBetween t₀ T,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im|) =
      ∑ ρ ∈ nontrivialZetaZerosBetween t₀ T,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |ρ.im|) := by
    refine sum_congr rfl fun ρ _ ↦ by ring
  rw [h_eq, sum_weighted_nontrivialZetaZerosBetween_eq_stieltjes ht₀T hderiv hcont]
  have h_pull :
      (∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) * (-1 / t ^ 2)) =
        -(∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2) := by
    have h_fn :
        (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * (-1 / t ^ 2)) =
          fun t : ℝ ↦ -((weightedZeroCountingFunction t : ℝ) / t ^ 2) := by
      ext t; ring
    rw [h_fn, intervalIntegral.integral_neg]
  rw [h_pull]
  ring

/-- **Multiplicity-Weighted Low-Frequency Stieltjes Identity for `nontrivialZetaZerosUpTo T`**:
Whenever `0 < t₀ ≤ T` and `weightedZeroCountingFunction t₀ = 0`,
$$\sum_{\rho \in \mathcal{Z}(T)} \frac{m_\rho}{|\operatorname{Im} \rho|}
  = \frac{N_{\text{mult}}(T)}{T} + \int_{t_0}^T \frac{N_{\text{mult}}(t)}{t^2} \, dt.$$ -/
theorem sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo_eq
    {t₀ T : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (h0 : weightedZeroCountingFunction t₀ = 0) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im|) =
      (weightedZeroCountingFunction T : ℝ) / T +
        ∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2 := by
  rw [nontrivialZetaZerosUpTo_eq_between_of_weightedZeroCountingFunction_eq_zero h0,
    sum_weighted_inv_abs_im_nontrivialZetaZerosBetween_eq ht₀ ht₀T, h0]
  simp

/-- `(fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 2)` is `IntervalIntegrable` on `t₀..T`
for `0 < t₀ ≤ T`. -/
theorem intervalIntegrable_weightedZeroCountingFunction_div_sq {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    IntervalIntegrable (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 2) volume t₀ T := by
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / t ^ 2) (Set.Icc t₀ T) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht_pos.ne')
  have h := intervalIntegrable_weightedZeroCountingFunction_mul ht₀T hcont
  simpa only [mul_one_div] using h

/-- Whenever `0 < t₀` and `weightedZeroCountingFunction t₀ = 0`, every `ρ ∈ nontrivialZetaZerosUpTo
T`
satisfies `(analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) /
|ρ.im|`. -/
theorem sum_weighted_inv_norm_le_sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo
    {t₀ T : ℝ} (ht₀ : 0 < t₀) (h0 : weightedZeroCountingFunction t₀ = 0) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
      ∑ ρ ∈ nontrivialZetaZerosUpTo T, (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| := by
  rw [nontrivialZetaZerosUpTo_eq_between_of_weightedZeroCountingFunction_eq_zero h0]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  have him_gt : t₀ < |ρ.im| := (mem_nontrivialZetaZerosBetween.mp hρ).2.2
  have him_pos : 0 < |ρ.im| := ht₀.trans him_gt
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) him_pos (Complex.abs_im_le_norm ρ)

/-- **Multiplicity-Weighted Low-Frequency Stieltjes Bound on $\sum_{\rho \in \mathcal{Z}(T)}
\frac{m_\rho}{\|\rho\|}$**:
If `0 < t₀ ≤ T`, `weightedZeroCountingFunction t₀ = 0`, and
`(weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D` for all `t ∈ Set.Icc t₀ T`,
then:
$$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{m_\rho}{\|\rho\|}
  \le \frac{a}{2} (\log T)^2 + (a + C) \log T + C + \frac{D}{t_0}
      - \frac{a}{2} (\log t_0)^2 - C \log t_0.$$ -/
theorem sum_weighted_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt
    {t₀ T a C D : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (hN_bound : ∀ t ∈ Set.Icc t₀ T,
      (weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
      a / 2 * (Real.log T) ^ 2 + (a + C) * Real.log T + C + D / t₀ -
        a / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀ := by
  have hT_pos : 0 < T := ht₀.trans_le ht₀T
  have hT_ne : T ≠ 0 := hT_pos.ne'
  refine (sum_weighted_inv_norm_le_sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo ht₀ h0).trans ?_
  rw [sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo_eq ht₀ ht₀T h0]
  have hNT_le : (weightedZeroCountingFunction T : ℝ) / T ≤ a * Real.log T + C + D / T := by
    have hT_in : T ∈ Set.Icc t₀ T := ⟨ht₀T, le_rfl⟩
    have h1 : (weightedZeroCountingFunction T : ℝ) / T ≤
        (a * T * Real.log T + C * T + D) / T :=
      div_le_div_of_nonneg_right (hN_bound T hT_in) hT_pos.le
    have h2 : (a * T * Real.log T + C * T + D) / T = a * Real.log T + C + D / T := by
      field_simp [hT_ne]
    rwa [h2] at h1
  have hint_B :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 2) volume t₀ T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀T]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 2) (pow_ne_zero 2 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  have hint_le :
      (∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2) ≤
        (a / 2 * (Real.log T) ^ 2 + C * Real.log T - D / T) -
          (a / 2 * (Real.log t₀) ^ 2 + C * Real.log t₀ - D / t₀) := by
    rw [← intervalIntegral_riemannVonMangoldt_div_sq ht₀ ht₀T a C D]
    refine intervalIntegral.integral_mono_on ht₀T
      (intervalIntegrable_weightedZeroCountingFunction_div_sq ht₀ ht₀T) hint_B fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact div_le_div_of_nonneg_right (hN_bound t ht) (by positivity)
  linarith

/-- **Multiplicity-Weighted Stieltjes Identity for the Quadratic Zero Tail $\sum_{T < |\gamma| \le
U} \frac{m_\rho}{\gamma^2}$**:
For `0 < T ≤ U`,
$$\sum_{\rho \in \mathcal{Z}(T, U)} \frac{m_\rho}{|\operatorname{Im} \rho|^2}
  = \frac{N_{\text{mult}}(U)}{U^2} - \frac{N_{\text{mult}}(T)}{T^2}
    + 2 \int_T^U \frac{N_{\text{mult}}(t)}{t^3} \, dt.$$ -/
theorem sum_weighted_inv_sq_nontrivialZetaZerosBetween_eq {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) =
      (weightedZeroCountingFunction U : ℝ) / U ^ 2 -
        (weightedZeroCountingFunction T : ℝ) / T ^ 2 +
        2 * ∫ t in T..U, (weightedZeroCountingFunction t : ℝ) / t ^ 3 := by
  have hderiv : ∀ t ∈ Set.Icc T U, HasDerivAt (fun x : ℝ ↦ 1 / x ^ 2) (-2 / t ^ 3) t :=
    fun t ht ↦ hasDerivAt_one_div_sq (hT.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ ↦ -2 / t ^ 3) (Set.Icc T U) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := hT.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht_pos.ne')
  have h_eq :
      (∑ ρ ∈ nontrivialZetaZerosBetween T U,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) =
      ∑ ρ ∈ nontrivialZetaZerosBetween T U,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |ρ.im| ^ 2) := by
    refine sum_congr rfl fun ρ _ ↦ by ring
  rw [h_eq, sum_weighted_nontrivialZetaZerosBetween_eq_stieltjes hTU hderiv hcont]
  have h_pull :
      (∫ t in T..U, (weightedZeroCountingFunction t : ℝ) * (-2 / t ^ 3)) =
        -2 * ∫ t in T..U, (weightedZeroCountingFunction t : ℝ) / t ^ 3 := by
    have h_fn :
        (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * (-2 / t ^ 3)) =
          fun t : ℝ ↦ -2 * ((weightedZeroCountingFunction t : ℝ) / t ^ 3) := by
      ext t; ring
    rw [h_fn, intervalIntegral.integral_const_mul]
  rw [h_pull]
  ring

/-- `(fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 3)` is `IntervalIntegrable` on `T..U`
for `0 < T ≤ U`. -/
theorem intervalIntegrable_weightedZeroCountingFunction_div_cube {T U : ℝ}
    (hT : 0 < T) (hTU : T ≤ U) :
    IntervalIntegrable (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 3) volume T U := by
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / t ^ 3) (Set.Icc T U) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := hT.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht_pos.ne')
  have h := intervalIntegrable_weightedZeroCountingFunction_mul hTU hcont
  simpa only [mul_one_div] using h

/-- **Closed-Form Evaluation of the Cubic Riemann–von Mangoldt Stieltjes Integral**:
For `0 < T ≤ U` and any constants `a, C, D : ℝ`,
$$\int_T^U \frac{a t \log t + C t + D}{t^3} \, dt
  = \left(\frac{a \log T + a + C}{T} + \frac{D}{2 T^2}\right)
    - \left(\frac{a \log U + a + C}{U} + \frac{D}{2 U^2}\right).$$ -/
theorem intervalIntegral_riemannVonMangoldt_div_cube {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U)
    (a C D : ℝ) :
    (∫ t : ℝ in T..U, (a * t * Real.log t + C * t + D) / t ^ 3) =
      ((a * Real.log T + a + C) / T + D / (2 * T ^ 2)) -
        ((a * Real.log U + a + C) / U + D / (2 * U ^ 2)) := by
  have hderiv : ∀ t ∈ Set.uIcc T U,
      HasDerivAt (fun x : ℝ ↦ (-a * Real.log x - a - C) * x⁻¹ - (D / 2) * (x ^ 2)⁻¹)
        ((a * t * Real.log t + C * t + D) / t ^ 3) t := by
    intro t ht
    rw [Set.uIcc_of_le hTU] at ht
    have ht_pos : 0 < t := hT.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hd1 : HasDerivAt (fun x : ℝ ↦ -a * Real.log x - a - C) (-a * t⁻¹) t :=
      (((Real.hasDerivAt_log ht_ne).const_mul (-a)).sub_const a).sub_const C
    have hd1_mul := hd1.mul (hasDerivAt_inv ht_ne)
    have hd2 : HasDerivAt (fun x : ℝ ↦ (D / 2) * (x ^ 2)⁻¹)
        ((D / 2) * (-(2 * t ^ (2 - 1)) / (t ^ 2) ^ 2)) t :=
      ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht_ne)).const_mul (D / 2)
    refine (hd1_mul.sub hd2).congr_deriv ?_
    field_simp [ht_ne]
    ring
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 3) volume T U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := hT.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 3) (pow_ne_zero 3 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

end ConjectureMachines.Semantics.Riemann.WeightedStieltjes
