/- GID: D5/S3/Arith/Robin/ForwardKernel/PairedLaplace
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PairedLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The logarithmic forward response has a paired Laplace representation with a holomorphic quadratic-growth regular part. -/

import D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth
import D5.S3.Arith.Robin.ForwardKernel.Fubini
import D5.S3.Weil.ZeroData.PairedXiExpansion
import D5.S3.Analytic.Oscillation.FejerDirichletTransfer
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingClosure
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace
import D5.S3.Weil.Mertens.Cryptids.DigammaBinet
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace D5.S3.Arith.Robin.ForwardKernel

open Set MeasureTheory Filter
open scoped Topology BigOperators
open ForwardKernel.MellinConvergence (forwardMellin response_measurable forwardMellin_integrable)
open D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth
  (VonKochBound forward_kernel_mellin_polynomial_remainder)
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Analytic.Laplace.PairedPoleRegularity
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum)
open D5.S3.Weil.ZeroData.PairedXiExpansion (PoleFree PairedXiExpansion)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Zeros.CompletedZeta (xiReading)
open ConjectureMachines.Semantics.Riemann.DigammaBinet
open ForwardKernel.Transport (forwardResponse)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The logarithmic coordinate form of the forward response, cut off at `x₀`. -/
def forwardLog (x0 : ℝ) (y : ℝ) : ℝ :=
  if Real.log x0 < y then forwardResponse (Real.exp y) else 0

/-- The regular term left after replacing the zeta logarithmic derivative by ξ. -/
def forwardRegularPart (R : ℂ → ℂ) (s : ℂ) : ℂ :=
  R s + 1 / (2 * (s + 1 / 2)) - (Real.log Real.pi : ℂ) / 4 +
    Complex.digamma ((s + 1 / 2) / 2) / 4

theorem laplace_forwardLog_eq_forwardMellin
    {x0 : ℝ} (hx0 : 3 ≤ x0) (s : ℂ) :
    laplace (forwardLog x0) s = forwardMellin x0 s := by
  have hx0pos : 0 < x0 := by linarith
  have hlog0 : 0 ≤ Real.log x0 := by
    exact Real.log_nonneg (by linarith [hx0])
  let g : ℝ → ℂ := fun x =>
    (forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1)
  rw [laplace, integral_Ici_eq_integral_Ioi]
  have hcut : (fun y : ℝ =>
      (forwardLog x0 y : ℂ) * Complex.exp (-s * (y : ℂ))) =ᵐ[volume.restrict (Ioi 0)]
      (Ioi (Real.log x0)).indicator (fun y : ℝ =>
        (forwardResponse (Real.exp y) : ℂ) * Complex.exp (-s * (y : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    by_cases h : Real.log x0 < y
    · simp only [forwardLog, if_pos h, Set.indicator_of_mem (show y ∈ Ioi (Real.log x0) from h)]
    · have hy' : y ≤ Real.log x0 := le_of_not_gt h
      rw [forwardLog, if_neg h, Set.indicator_of_notMem (by simp [hy'])]
      simp
  rw [integral_congr_ae hcut]
  change (∫ y : ℝ, (Ioi (Real.log x0)).indicator
      (fun y : ℝ => (forwardResponse (Real.exp y) : ℂ) *
        Complex.exp (-s * (y : ℂ))) y ∂(volume.restrict (Ioi (0 : ℝ)))) = _
  have hind := integral_indicator (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun y : ℝ => (forwardResponse (Real.exp y) : ℂ) *
      Complex.exp (-s * (y : ℂ))) (s := Ioi (Real.log x0)) measurableSet_Ioi
  rw [hind]
  simp only [Measure.restrict_restrict, measurableSet_Ioi]
  rw [show Ioi (Real.log x0) ∩ Ioi (0 : ℝ) = Ioi (Real.log x0) by
    ext y; simp [hlog0]]
  calc
    _ = ∫ y in Ioi (Real.log x0), Real.exp y • g (Real.exp y) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp [g]
      have hey : (Real.exp y : ℝ) ≠ 0 := Real.exp_ne_zero _
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hey)]
      rw [Complex.ofReal_exp y,
        Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)]
      rw [show (↑y : ℂ) * (-s - 1) = -s * ↑y - ↑y by ring]
      rw [← mul_assoc, mul_comm (Complex.exp (y : ℂ))
        (forwardResponse (Real.exp y) : ℂ), mul_assoc]
      rw [← Complex.exp_add]
      ring_nf
    _ = ∫ x in Ioi (Real.exp (Real.log x0)), g x :=
      integral_comp_exp_Ioi g (Real.log x0)
    _ = forwardMellin x0 s := by
      rw [Real.exp_log hx0pos]
      rfl

theorem forwardRegularPart_holomorphic
    {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R {s : ℂ | -(1 / 5 : ℝ) < s.re}) :
    DifferentiableOn ℂ (forwardRegularPart R)
      {s : ℂ | -(1 / 5 : ℝ) < s.re} := by
  intro s hs
  unfold forwardRegularPart
  let S : Set ℂ := {s : ℂ | -(1 / 5 : ℝ) < s.re}
  have hdiv : DifferentiableOn ℂ (fun z : ℂ => 1 / (2 * (z + 1 / 2))) S := by
    apply (differentiableOn_const (1 : ℂ)).div
      ((differentiableOn_id.add (differentiableOn_const (1 / 2 : ℂ))).const_mul 2)
    intro z hz hzero
    dsimp [S] at hz
    have hz' := congrArg Complex.re hzero
    simp at hz'
    linarith [hz]
  have hdig : DifferentiableOn ℂ (fun z : ℂ =>
      Complex.digamma ((z + 1 / 2) / 2) / 4) S := by
    let f : ℂ → ℂ := fun z => (z + 1 / 2) / 2
    have hf : DifferentiableOn ℂ f S := by
      exact (differentiableOn_id.add (differentiableOn_const (1 / 2 : ℂ))).div
        (differentiableOn_const 2) (by intro z hz h; norm_num at h)
    have hmap : MapsTo f S {z : ℂ | 0 < z.re} := by
      intro z hz
      dsimp [f]
      dsimp [S] at hz
      norm_num
      linarith
    simpa [f, div_eq_mul_inv, mul_comm] using
      (DifferentiableOn.const_mul (differentiableOn_digamma_rightHalfPlane.comp hf hmap) (1 / 4 : ℂ))
  have hq : DifferentiableWithinAt ℂ (fun z : ℂ =>
      1 / (2 * (z + 1 / 2)) - (Real.log Real.pi : ℂ) / 4 +
        Complex.digamma ((z + 1 / 2) / 2) / 4)
      {s : ℂ | -(1 / 5 : ℝ) < s.re} s := by
    exact ((hdiv.sub (differentiableOn_const _)).add hdig) s hs
  have hh := (hR s hs).add hq
  convert hh using 1 <;> (try ext z) <;> (try funext z) <;>
    simp only [Pi.add_apply] <;> ring

set_option maxHeartbeats 1000000 in
lemma forwardRegularPart_gaussian_growth
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

theorem forwardRegularPart_growth
    {R : ℂ → ℂ}
    (hR : ∀ δ : ℝ, 0 < δ → δ < 1 / 5 →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
        -(1 / 5 : ℝ) + δ ≤ s.re → s.re ≤ 1 →
        ‖R s‖ ≤ C * (1 + |s.im|) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      |s.re| ≤ (1 / 20 : ℝ) →
      ‖forwardRegularPart R s‖ ≤
        C * (1 + |s.im|) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := forwardRegularPart_gaussian_growth hR
  refine ⟨C, hC, fun s hs => hb s ?_ ?_⟩
  · linarith [(abs_le.mp hs).1]
  · linarith [(abs_le.mp hs).2]

noncomputable def forwardPairedLaplaceData
    (hRH : RiemannHypothesis)
    (hVK : VonKochBound)
    (hH : PairedXiExpansion hRH)
    {x0 : ℝ} (hx0 : 3 ≤ x0) :
    PairedLaplaceData
      (zetaSpectrum hRH) (forwardLog x0) 2 := by
  let hRem := forward_kernel_mellin_polynomial_remainder hVK hx0
  let R : ℂ → ℂ := Classical.choose hRem
  have hRhol : DifferentiableOn ℂ R {s : ℂ | -(1 / 5 : ℝ) < s.re} :=
    (Classical.choose_spec hRem).1
  have hRmellin : ∀ s : ℂ, 1 / 2 < s.re →
      forwardMellin x0 s =
        -(1 / 2 : ℂ) * (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)) -
          1 / (2 * (s - 1 / 2)) + R s :=
    (Classical.choose_spec hRem).2.1
  have hRgrowth : ∀ δ : ℝ, 0 < δ → δ < 1 / 5 →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) + δ ≤ s.re → s.re ≤ 1 →
        ‖R s‖ ≤ C * (1 + |s.im|) ^ 2 :=
    (Classical.choose_spec hRem).2.2
  have E : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ) := by
    obtain ⟨C, t0, hC⟩ :=
      D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth.vonKoch_power_bound hVK
        (show 0 < (1 / 4 : ℝ) by norm_num)
    exact ⟨C, t0, by simpa only [show (1 / 2 : ℝ) + 1 / 4 = 3 / 4 by norm_num] using hC⟩
  refine {
    measurable := ?_,
    local_bound := ?_,
    initial_convergence := ?_,
    eta := 1 / 10,
    eta_pos := by norm_num,
    eta_lt := by norm_num,
    J := forwardRegularPart R,
    holomorphic := ?_,
    growth := ?_,
    identity := ?_ }
  · exact Measurable.ite measurableSet_Ioi
      (response_measurable.comp Real.measurable_exp) measurable_const
  · intro A hA
    obtain ⟨C, hC, hErr⟩ :=
      MellinConvergence.error_power_bound (show 0 ≤ (3 / 4 : ℝ) by norm_num) E
    let q : ℝ := 3 / 4 - 3 / 10
    let B : ℝ := 2 * C * (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.exp A) ^ q
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro y hy
    by_cases hcut : Real.log x0 < y
    · have hyx : 3 ≤ Real.exp y := by
        have hlogx : Real.log x0 < y := hcut
        have hxexp : x0 ≤ Real.exp y := by
          rw [← Real.exp_log (by linarith : 0 < x0)]
          exact Real.exp_le_exp.mpr hlogx.le
        exact hx0.trans hxexp
      have hyA : y ≤ A := hy.2
      have hpow := MellinConvergence.forwardResponse_power_bound hC
        (show 0 ≤ (3 / 4 : ℝ) by norm_num) hErr hyx
      rw [forwardLog, if_pos hcut]
      have hxy : Real.exp y ≤ Real.exp A := Real.exp_le_exp.mpr hyA
      have hq : 0 ≤ q := by dsimp [q]; norm_num
      have hrpow : (Real.exp y) ^ q ≤ (Real.exp A) ^ q :=
        Real.rpow_le_rpow (by positivity) hxy hq
      have hrewrite : (Real.exp y) ^ ((3 / 4 : ℝ) - 3 / 10) =
          (Real.exp y) ^ q := by rfl
      have hB : |forwardResponse (Real.exp y)| ≤ B := by
        calc
          |forwardResponse (Real.exp y)| ≤
              2 * C * (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.exp y) ^ q := by
                simpa [q] using hpow
          _ ≤ B := by
            dsimp [B]
            exact mul_le_mul_of_nonneg_left hrpow (by positivity)
      exact hB.trans (le_max_right _ _)
    · rw [forwardLog, if_neg hcut]
      simp
  · intro σ hσ
    let g : ℝ → ℂ := fun x =>
      (forwardResponse x : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1)
    have hg := MellinConvergence.forwardMellin_integrable
      (α := (3 / 4 : ℝ)) (show 0 ≤ (3 / 4 : ℝ) by norm_num) E hx0 (s := (σ : ℂ))
      (by norm_num; linarith [hσ])
    have hcomp : IntegrableOn (fun y : ℝ => Real.exp y • g (Real.exp y))
        (Ioi (Real.log x0)) :=
      by
        have hg' : IntegrableOn g (Ioi x0) := by
          simpa [g] using hg
        have hge : IntegrableOn g (Ioi (Real.exp (Real.log x0))) := by
          simpa [Real.exp_log (by linarith : 0 < x0)] using hg'
        exact (integrableOn_comp_exp_Ioi g (Real.log x0)).2 hge
    let F : ℝ → ℂ := fun y =>
      (forwardResponse (Real.exp y) : ℂ) * Complex.exp (-(σ : ℂ) * (y : ℂ))
    have hEq : EqOn (fun y : ℝ => Real.exp y • g (Real.exp y)) F
        (Ioi (Real.log x0)) := by
      intro y hy
      dsimp [F, g]
      have hey : (Real.exp y : ℝ) ≠ 0 := Real.exp_ne_zero _
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hey),
        Complex.ofReal_exp y,
        Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)]
      rw [show (↑y : ℂ) * (-(σ : ℂ) - 1) = -(σ : ℂ) * ↑y - ↑y by ring]
      rw [← mul_assoc, mul_comm (Complex.exp (y : ℂ))
        (forwardResponse (Real.exp y) : ℂ), mul_assoc]
      rw [← Complex.exp_add]
      ring_nf
    have hFi : IntegrableOn F (Ioi (Real.log x0)) := hcomp.congr_fun hEq measurableSet_Ioi
    have hFglob : Integrable ((Ioi (Real.log x0)).indicator F) :=
      (integrable_indicator_iff measurableSet_Ioi).2 hFi
    have hFglob0 : IntegrableOn ((Ioi (Real.log x0)).indicator F) (Ioi (0 : ℝ)) :=
      hFglob.integrableOn
    have hreal : IntegrableOn
        (fun y => (((Ioi (Real.log x0)).indicator F) y).re) (Ioi (0 : ℝ)) :=
      hFglob0.re
    have htarget : EqOn
        (fun y : ℝ => (forwardLog x0 y) * Real.exp (-σ * y))
        (fun y => (((Ioi (Real.log x0)).indicator F) y).re) (Ioi (0 : ℝ)) := by
      intro y hy
      by_cases hcut : Real.log x0 < y
      · change forwardLog x0 y * Real.exp (-σ * y) =
          (((if y ∈ Ioi (Real.log x0) then F y else 0) : ℂ)).re
        have hymem : y ∈ Ioi (Real.log x0) := hcut
        rw [if_pos hymem]
        simp only [forwardLog, if_pos hcut]
        dsimp [F]
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.neg_re, Complex.one_re]
        have harg : -↑σ * ↑y = ((-(σ * y) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [harg, Complex.exp_ofReal_re]
        ring
      · have hle : y ≤ Real.log x0 := le_of_not_gt hcut
        change forwardLog x0 y * Real.exp (-σ * y) =
          (((if y ∈ Ioi (Real.log x0) then F y else 0) : ℂ)).re
        have hymem : y ∉ Ioi (Real.log x0) := hcut
        rw [if_neg hymem]
        simp only [forwardLog, if_neg hcut]
        simp
    have htarget0 := hreal.congr_fun (fun y hy => (@htarget y hy).symm) measurableSet_Ioi
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 htarget0
  · exact (forwardRegularPart_holomorphic hRhol).mono (by intro s hs; norm_num at *; linarith)
  · obtain ⟨C, hC, hJ⟩ := forwardRegularPart_growth hRgrowth
    refine ⟨C, hC, ?_⟩
    intro s hs
    norm_num at hs ⊢
    exact hJ s hs
  · intro s hs1 hs2
    have hPole : s ∈ PoleFree (zetaSpectrum hRH) := by
      intro j
      constructor
      · intro h
        have hr := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero] at hr
        have hr0 : s.re = 0 := by simpa using hr
        linarith
      · intro h
        have hr := congrArg Complex.re h
        simp only [Complex.add_re, Complex.neg_re, Complex.mul_re,
          Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
          neg_zero] at hr
        have hr0 : s.re = 0 := by simpa using hr
        linarith
    have hsum := (hH s hPole).tsum_eq
    have hxi := xi_logDeriv_right
      (s := s + 1 / 2) (by
        norm_num
        linarith)
    have hxi' : logDeriv xiReading ((1 / 2 : ℂ) + s) =
        1 / (s + 1 / 2) + 1 / (s - 1 / 2) -
          (Real.log Real.pi : ℂ) / 2 + Complex.digamma ((s + 1 / 2) / 2) / 2 +
          deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2) := by
      rw [show (1 / 2 : ℂ) + s = s + 1 / 2 by ring]
      convert hxi using 1 <;> ring
    have hzplus : s + 1 / 2 ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith
    have hzminus : s - 1 / 2 ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith
    have hxi'' : logDeriv xiReading ((1 / 2 : ℂ) + s) =
        2 * (1 / (2 * (s + 1 / 2))) + 2 * (1 / (2 * (s - 1 / 2))) -
          (Real.log Real.pi : ℂ) / 2 + Complex.digamma ((s + 1 / 2) / 2) / 2 +
          deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2) := by
      convert hxi' using 1 <;> field_simp [hzplus, hzminus] <;> ring
    have hm := hRmellin s hs1
    rw [laplace_forwardLog_eq_forwardMellin hx0 s]
    rw [hsum]
    rw [forwardRegularPart]
    linear_combination hm + (1 / 2 : ℂ) * hxi''

end
end D5.S3.Arith.Robin.ForwardKernel
