/- GID: D5/S3/Arith/Robin/ForwardKernel/GaussianLaplace
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/GaussianLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The forward paired Laplace regular part has quadratic growth throughout the Gaussian inversion strip. -/

import D5.S3.Analytic.Laplace.GaussianStripControl
import D5.S3.Arith.Robin.ForwardKernel.PairedLaplace

/-! Wider strip bounds for the regular part of the forward response transform. -/

namespace D5.S3.Arith.Robin.ForwardKernel

open D5.S3.Analytic.Laplace.PairedPoleRegularity
open D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth
open D5.S3.Weil.ZeroData.PairedXiExpansion (PairedXiExpansion)
open ConjectureMachines.Semantics.Riemann.DigammaBinet

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
private lemma forwardRegularPart_gaussian_growth
    {R : ℂ → ℂ}
    (hR : ∀ δ : ℝ, 0 < δ → δ < 1 / 5 →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
        -(1 / 5 : ℝ) + δ ≤ s.re → s.re ≤ 1 →
        ‖R s‖ ≤ C * (1 + |s.im|) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      -(1 / 6 : ℝ) ≤ s.re → s.re ≤ 3 / 4 →
      ‖forwardRegularPart R s‖ ≤ C * (1 + |s.im|) ^ 2 := by
  obtain ⟨CR, hCR, hRb⟩ := hR (1 / 30) (by norm_num) (by norm_num)
  refine ⟨CR + 20 + 10 * Real.pi + |Real.log Real.pi|, by positivity, ?_⟩
  intro s hsr hsu
  let w : ℂ := (s + 1 / 2) / 2
  have hwr : (1 / 6 : ℝ) ≤ w.re := by
    dsimp [w]
    norm_num [Complex.div_re, Complex.add_re]
    linarith
  have hwr' : w.re ≤ (5 / 8 : ℝ) := by
    dsimp [w]
    norm_num [Complex.div_re, Complex.add_re]
    linarith
  have hwn : (1 / 6 : ℝ) ≤ ‖w‖ := hwr.trans (Complex.re_le_norm w)
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hwn
  have hwinv : 1 / ‖w‖ ≤ (6 : ℝ) := by
    apply (div_le_iff₀ hwpos).2
    linarith
  have hwupper : ‖w‖ ≤ 1 + |s.im| := by
    have hre : |w.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |w.im| = |s.im| / 2 := by
      norm_num [w, Complex.div_im, Complex.add_im, abs_div]
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 1 + |s.im| / 2 := add_le_add hre him.le
      _ ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hlognorm : |Real.log ‖w‖| ≤ ‖w‖ + 1 / ‖w‖ := by
    apply abs_le.mpr
    constructor
    · have h := Real.neg_inv_le_log (norm_nonneg w)
      simp only [one_div]
      linarith [norm_nonneg w]
    · exact (Real.log_le_self (norm_nonneg w)).trans
        (le_add_of_nonneg_right (by positivity))
  have hlog : ‖Complex.log w‖ ≤ 1 + |s.im| + 6 + Real.pi := by
    have h := D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingClosure.norm_neg_log_le_abs_log_norm_add_pi w
    rw [norm_neg] at h
    calc
      ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := h
      _ ≤ ‖w‖ + 1 / ‖w‖ + Real.pi := by linarith
      _ ≤ 1 + |s.im| + 6 + Real.pi := by linarith
  have hdig0 := norm_digamma_sub_log_le_two_add_pi_div_four_norm
    (lt_of_lt_of_le (by norm_num) hwr)
  have herr : (2 + Real.pi) / (4 * ‖w‖) ≤ 2 * (2 + Real.pi) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hwpos)).2
    have hm := mul_le_mul_of_nonneg_left hwn
      (show 0 ≤ 8 * (2 + Real.pi) by positivity)
    nlinarith [Real.pi_pos]
  have hdig : ‖Complex.digamma w‖ ≤ 1 + |s.im| + 10 + 3 * Real.pi := by
    have hsum := norm_add_le (Complex.digamma w - Complex.log w) (Complex.log w)
    have hsum' : ‖Complex.digamma w‖ ≤
        ‖Complex.digamma w - Complex.log w‖ + ‖Complex.log w‖ := by
      simpa only [sub_add_cancel] using hsum
    exact (hsum'.trans (add_le_add (hdig0.trans herr) hlog)).trans (by linarith)
  have hden : (1 / 3 : ℝ) ≤ ‖s + 1 / 2‖ := by
    have h := Complex.re_le_norm (s + 1 / 2)
    norm_num at h
    linarith
  have hfrac : ‖1 / (2 * (s + 1 / 2))‖ ≤ (3 : ℝ) := by
    rw [norm_div, norm_mul]
    norm_num only [norm_one, Complex.norm_ofNat]
    have hdenpos : 0 < ‖s + 1 / 2‖ := lt_of_lt_of_le (by norm_num) hden
    apply (div_le_iff₀ (by positivity : 0 < 2 * ‖s + 1 / 2‖)).2
    linarith
  have hconst : ‖(Real.log Real.pi : ℂ) / 4‖ ≤ |Real.log Real.pi| := by
    norm_num [norm_div, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_nonneg (Real.log Real.pi)]
  have hd4 : ‖Complex.digamma w / 4‖ ≤
      (1 + |s.im| + 10 + 3 * Real.pi) / 4 := by
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right hdig (by norm_num)
  have hR0 := hRb s (by linarith) (by linarith)
  have hsq : 1 + |s.im| ≤ (1 + |s.im|) ^ 2 := by
    nlinarith [abs_nonneg s.im]
  have hsq1 : 1 ≤ (1 + |s.im|) ^ 2 := by
    nlinarith [abs_nonneg s.im]
  have hpis : Real.pi ≤ Real.pi * (1 + |s.im|) ^ 2 :=
    le_mul_of_one_le_right Real.pi_pos.le hsq1
  have hlogs : |Real.log Real.pi| ≤
      |Real.log Real.pi| * (1 + |s.im|) ^ 2 :=
    le_mul_of_one_le_right (abs_nonneg _) hsq1
  have hsum : ‖forwardRegularPart R s‖ ≤
      ‖R s‖ + ‖1 / (2 * (s + 1 / 2))‖ +
        ‖(Real.log Real.pi : ℂ) / 4‖ + ‖Complex.digamma w / 4‖ := by
    have ha := norm_add_le (R s) (1 / (2 * (s + 1 / 2)))
    have hb := norm_sub_le (R s + 1 / (2 * (s + 1 / 2)))
      ((Real.log Real.pi : ℂ) / 4)
    have hc := norm_add_le
      (R s + 1 / (2 * (s + 1 / 2)) - (Real.log Real.pi : ℂ) / 4)
      (Complex.digamma w / 4)
    change ‖forwardRegularPart R s‖ ≤ _ at hc
    linarith
  calc
    ‖forwardRegularPart R s‖ ≤ CR * (1 + |s.im|) ^ 2 + 3 +
        |Real.log Real.pi| + (1 + |s.im| + 10 + 3 * Real.pi) / 4 :=
      hsum.trans (by linarith)
    _ ≤ (CR + 20 + 10 * Real.pi + |Real.log Real.pi|) *
        (1 + |s.im|) ^ 2 := by nlinarith [Real.pi_pos]

theorem forwardPairedLaplaceData_gaussianStrip
    (hRH : RiemannHypothesis) (hVK : VonKochBound) (hXi : PairedXiExpansion hRH) :
    GaussianStripControl
      (forwardPairedLaplaceData hRH hVK hXi (x0 := 3) (by norm_num)).J := by
  let hRem := forward_kernel_mellin_polynomial_remainder hVK (x0 := 3) (by norm_num)
  let R : ℂ → ℂ := Classical.choose hRem
  change GaussianStripControl (forwardRegularPart R)
  exact ⟨(forwardRegularPart_holomorphic (Classical.choose_spec hRem).1).mono
    (fun _ hs => hs.1),
    forwardRegularPart_gaussian_growth (Classical.choose_spec hRem).2.2⟩

end
end D5.S3.Arith.Robin.ForwardKernel
