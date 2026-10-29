/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionFiniteSlit
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed finite-slit boundary patches in logarithmic coordinates. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionReciprocalSeries
import Mathlib.Topology.Piecewise

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionFiniteSlit

private def bankPatch (f U : ℂ → ℂ) (rho : ℝ) (z : ℂ) : ℂ :=
  if ‖z - 1‖ ≤ rho then U z else f z

private theorem off_cut_of_collar_complement {rho R : ℝ} (hR : R < 1 + rho / 2)
    {z : ℂ} (hz : ‖z‖ ≤ R) (hd : rho / 2 < ‖z - 1‖) :
    z ∈ CompositionContinuation.omega := by
  by_contra h
  change ¬ (1 - z ∈ Complex.slitPlane) at h
  rw [Complex.mem_slitPlane_iff] at h
  push Not at h
  have hre : 1 ≤ z.re := by
    have hx := h.1
    simp only [sub_re, one_re] at hx
    linarith
  have him : z.im = 0 := by simpa only [sub_im, one_im, zero_sub, neg_eq_zero] using h.2
  have hreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hn : ‖z‖ = z.re := by
    calc
      ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hreal
      _ = z.re := by simp [Complex.norm_real, abs_of_nonneg (by linarith : 0 ≤ z.re)]
  have hdn : ‖z - 1‖ = z.re - 1 := by
    calc
      ‖z - 1‖ = ‖((z.re - 1 : ℝ) : ℂ)‖ := by
        simp only [Complex.ofReal_sub, Complex.ofReal_one]
        exact congrArg (fun t : ℂ ↦ ‖t - 1‖) hreal
      _ = z.re - 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ z.re - 1)]
  rw [hn] at hz
  rw [hdn] at hd
  linarith

private theorem bank_patch_agrees {f U : ℂ → ℂ} {rho : ℝ} {S : Set ℂ}
    (hag : ∀ z ∈ S, ‖z - 1‖ ≤ rho → z ∈ CompositionContinuation.omega → U z = f z)
    {z : ℂ} (hz : z ∈ S) (homega : z ∈ CompositionContinuation.omega) :
    bankPatch f U rho z = f z := by
  by_cases hd : ‖z - 1‖ ≤ rho
  · simp only [bankPatch, ite_eq_left hd]
    exact hag z hz hd homega
  · simp [bankPatch, hd]

private theorem bank_patch_continuous {f U : ℂ → ℂ} {rho R R0 : ℝ} {S : Set ℂ}
    (hrho : 0 < rho) (hR : R < 1 + rho / 2) (hR0 : R < R0)
    (hf : AnalyticOnNhd ℂ f {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (hU : ContinuousOn U {z | ‖z - 1‖ ≤ rho ∧ z ∈ S})
    (hag : ∀ z ∈ S, ‖z - 1‖ ≤ rho → z ∈ CompositionContinuation.omega → U z = f z) :
    ContinuousOn (bankPatch f U rho) {z | ‖z‖ ≤ R ∧ z ∈ S} := by
  intro z hz
  have hncont : Continuous (fun w : ℂ ↦ ‖w - 1‖) := by fun_prop
  by_cases hd : ‖z - 1‖ < rho
  · have hloc : {w : ℂ | ‖w - 1‖ ≤ rho ∧ w ∈ S} ∈
        𝓝[{w : ℂ | ‖w‖ ≤ R ∧ w ∈ S}] z := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hncont.continuousAt.eventually (gt_mem_nhds hd))] with w hw hwd
      exact ⟨hwd.le, hw.2⟩
    apply ((hU z ⟨hd.le, hz.2⟩).mono_of_mem_nhdsWithin hloc).congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [hloc] with w hw
    simp [bankPatch, hw.1]
  · have hlarge : rho / 2 < ‖z - 1‖ := by linarith [not_lt.mp hd]
    have hzomega := off_cut_of_collar_complement hR hz.1 hlarge
    have hloc : ∀ᶠ w in 𝓝[{w : ℂ | ‖w‖ ≤ R ∧ w ∈ S}] z,
        bankPatch f U rho w = f w := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hncont.continuousAt.eventually (lt_mem_nhds hlarge))] with w hw hwd
      exact bank_patch_agrees hag hw.2 (off_cut_of_collar_complement hR hw.1 hwd)
    exact (hf z ⟨hzomega, hz.1.trans_lt hR0⟩).continuousAt.continuousWithinAt
      |>.congr_of_eventuallyEq_of_mem hloc hz

private def logLift (F G : ℂ → ℂ) (w : ℂ) : ℂ :=
  if w.im ≤ Real.pi then F (Complex.exp w) else G (Complex.exp w)

private theorem exp_im_nonneg {w : ℂ} (h0 : 0 ≤ w.im) (hpi : w.im ≤ Real.pi) :
    0 ≤ (Complex.exp w).im := by
  rw [Complex.exp_im]
  exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_mem_Icc ⟨h0, hpi⟩)

private theorem exp_im_nonpos {w : ℂ} (hpi : Real.pi ≤ w.im) (h2pi : w.im ≤ 2 * Real.pi) :
    (Complex.exp w).im ≤ 0 := by
  rw [Complex.exp_im, ← Real.sin_sub_two_pi w.im]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))

private theorem exp_strip_omega {w : ℂ} (h0 : 0 < w.im) (h2pi : w.im < 2 * Real.pi) :
    Complex.exp w ∈ CompositionContinuation.omega := by
  change 1 - Complex.exp w ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  rcases lt_trichotomy w.im Real.pi with hpi | hpi | hpi
  · right
    have hpos : 0 < (Complex.exp w).im := by
      rw [Complex.exp_im]
      exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hpi)
    simpa only [sub_im, one_im, zero_sub, neg_ne_zero] using hpos.ne'
  · left
    simp only [sub_re, one_re, Complex.exp_re, hpi, Real.cos_pi, mul_neg_one]
    linarith [Real.exp_pos w.re]
  · right
    have hneg : (Complex.exp w).im < 0 := by
      rw [Complex.exp_im, ← Real.sin_sub_two_pi w.im]
      exact mul_neg_of_pos_of_neg (Real.exp_pos _)
        (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))
    simpa only [sub_im, one_im, zero_sub, neg_ne_zero] using hneg.ne

private theorem log_lift_continuous {f F G : ℂ → ℂ} {a b R : ℝ}
    (hab : a ≤ b) (hb : Real.exp b ≤ R)
    (hF : ContinuousOn F {z | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hG : ContinuousOn G {z | ‖z‖ ≤ R ∧ z.im ≤ 0})
    (hFag : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega → F z = f z)
    (hGag : ∀ z, ‖z‖ ≤ R → z.im ≤ 0 → z ∈ CompositionContinuation.omega → G z = f z) :
    ContinuousOn (logLift F G) (Icc a b ×ℂ Icc 0 (2 * Real.pi)) := by
  have hnorm : ∀ w ∈ Icc a b ×ℂ Icc 0 (2 * Real.pi), ‖Complex.exp w‖ ≤ R := by
    intro w hw
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw.1.2).trans hb
  apply ContinuousOn.if
  · intro w hw
    have hpi : w.im = Real.pi := by
      simpa only [Complex.frontier_setOfPred_im_le, mem_ofPred_eq] using hw.2
    have hwomega := exp_strip_omega (by rw [hpi]; exact Real.pi_pos)
      (by rw [hpi]; linarith [Real.pi_pos])
    exact (hFag _ (hnorm w hw.1) (exp_im_nonneg hw.1.2.1 (by rw [hpi])) hwomega).trans
      (hGag _ (hnorm w hw.1) (exp_im_nonpos (by rw [hpi]) hw.1.2.2) hwomega).symm
  · apply hF.comp Complex.continuous_exp.continuousOn
    intro w hw
    have hpi : w.im ≤ Real.pi := by
      have hcl : closure {w : ℂ | w.im ≤ Real.pi} = {w : ℂ | w.im ≤ Real.pi} :=
        (isClosed_le Complex.continuous_im continuous_const).closure_eq
      have hw' := hw.2
      rw [hcl] at hw'
      exact hw'
    exact ⟨hnorm w hw.1, exp_im_nonneg hw.1.2.1 hpi⟩
  · apply hG.comp Complex.continuous_exp.continuousOn
    intro w hw
    have hpi : Real.pi ≤ w.im := by
      have hcl : closure {w : ℂ | ¬ w.im ≤ Real.pi} = {w : ℂ | Real.pi ≤ w.im} := by
        simp only [not_le]
        exact Complex.closure_setOfPred_lt_im _
      have hw' := hw.2
      rw [hcl] at hw'
      exact hw'
    exact ⟨hnorm w hw.1, exp_im_nonpos hpi hw.1.2.2⟩

private theorem log_lift_agrees {f F G : ℂ → ℂ} {R : ℝ}
    (hFag : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega → F z = f z)
    (hGag : ∀ z, ‖z‖ ≤ R → z.im ≤ 0 → z ∈ CompositionContinuation.omega → G z = f z)
    {w : ℂ} (hn : ‖Complex.exp w‖ ≤ R) (h0 : 0 < w.im) (h2pi : w.im < 2 * Real.pi) :
    logLift F G w = f (Complex.exp w) := by
  have homega := exp_strip_omega h0 h2pi
  by_cases hpi : w.im ≤ Real.pi
  · exact (ite_eq_left hpi).trans (hFag _ hn (exp_im_nonneg h0.le hpi) homega)
  · exact (ite_eq_right hpi).trans (hGag _ hn (exp_im_nonpos (not_le.mp hpi).le h2pi.le) homega)

private theorem log_lift_differentiable {f F G : ℂ → ℂ} {a b R R0 : ℝ}
    (hb : Real.exp b ≤ R) (hR0 : R < R0)
    (hf : AnalyticOnNhd ℂ f {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (hFag : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega → F z = f z)
    (hGag : ∀ z, ‖z‖ ≤ R → z.im ≤ 0 → z ∈ CompositionContinuation.omega → G z = f z) :
    DifferentiableOn ℂ (logLift F G) (Ioo a b ×ℂ Ioo 0 (2 * Real.pi)) := by
  intro w hw
  have hnorm : ‖Complex.exp w‖ ≤ R := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw.1.2.le).trans hb
  have hd := (hf _ ⟨exp_strip_omega hw.2.1 hw.2.2, hnorm.trans_lt hR0⟩).differentiableAt
    |>.comp w differentiable_exp.differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hw] with v hv
  exact (log_lift_agrees hFag hGag (by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hv.1.2.le).trans hb) hv.2.1 hv.2.2)

private theorem actual_boundary_patches (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    ∃ R R0 : ℝ, 1 < R ∧ R < R0 ∧
      AnalyticOnNhd ℂ (CompositionReciprocalSeries.reciprocal head tail ell)
        {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0} ∧
      ∃ F G : ℂ → ℂ,
        ContinuousOn F {z | ‖z‖ ≤ R ∧ 0 ≤ z.im} ∧
        ContinuousOn G {z | ‖z‖ ≤ R ∧ z.im ≤ 0} ∧
        (∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega →
          F z = CompositionReciprocalSeries.reciprocal head tail ell z) ∧
        (∀ z, ‖z‖ ≤ R → z.im ≤ 0 → z ∈ CompositionContinuation.omega →
          G z = CompositionReciprocalSeries.reciprocal head tail ell z) ∧
        (F 1).im = 0 ∧
        (∀ x : ℝ, 1 ≤ x → x ≤ R → G x = conj (F x)) ∧
        ∀ x : ℝ, 1 < x → x ≤ R → (F x).im < 0 := by
  obtain ⟨hag, han, R0, hR0, hne⟩ := CompositionZeroFreeCollar.result head tail
  obtain ⟨rho, hrho, hrho1, _hbnz, _hend, U, V, hU, hV, hUag, hVag,
    hU1, _hV1, hconj, hneg⟩ := CompositionBanks.result head tail ell
  let R : ℝ := 1 + min (R0 - 1) (rho / 2) / 2
  have hmin : 0 < min (R0 - 1) (rho / 2) := lt_min (by linarith) (by linarith)
  have hR : 1 < R := by dsimp [R]; linarith
  have hRR0 : R < R0 := by
    dsimp [R]
    linarith [min_le_left (R0 - 1) (rho / 2)]
  have hRrho : R < 1 + rho / 2 := by
    dsimp [R]
    linarith [min_le_right (R0 - 1) (rho / 2)]
  let f := CompositionReciprocalSeries.reciprocal head tail ell
  have hf : AnalyticOnNhd ℂ f {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0} := by
    intro z hz
    exact ((han z hz.1).pow (ell : ℕ)).inv (pow_ne_zero _ (hne z hz.1 hz.2))
  have hformula : ∀ z : ℂ, ‖z - 1‖ ≤ rho →
      f z = (z ^ CompositionDisk.depth tail /
        CompositionContinuation.continued (head :: tail) z) ^ (ell : ℕ) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hz0
      simp only [hz0, zero_sub, norm_neg, norm_one] at hz
      linarith
    simp only [f, CompositionReciprocalSeries.reciprocal,
      CompositionZeroFreeCollar.normalizedContinuation, if_neg hz0, ← inv_pow, inv_div]
  have hUeq : ∀ z ∈ {z : ℂ | 0 ≤ z.im}, ‖z - 1‖ ≤ rho →
      z ∈ CompositionContinuation.omega → U z = f z := by
    intro z hzim hz homega
    exact (hUag z hz hzim homega).trans (hformula z hz).symm
  have hVeq : ∀ z ∈ {z : ℂ | z.im ≤ 0}, ‖z - 1‖ ≤ rho →
      z ∈ CompositionContinuation.omega → V z = f z := by
    intro z hzim hz homega
    exact (hVag z hz hzim homega).trans (hformula z hz).symm
  let F := bankPatch f U rho
  let G := bankPatch f V rho
  refine ⟨R, R0, hR, hRR0, hf, F, G,
    bank_patch_continuous hrho hRrho hRR0 hf hU hUeq,
    bank_patch_continuous hrho hRrho hRR0 hf hV hVeq,
    (fun z _ hzim homega ↦ bank_patch_agrees hUeq hzim homega),
    (fun z _ hzim homega ↦ bank_patch_agrees hVeq hzim homega), ?_, ?_, ?_⟩
  · simp only [F, bankPatch, sub_self, norm_zero, if_pos hrho.le, hU1]
    split_ifs <;>
      simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_im, Complex.zero_im]
  · intro x hx hxR
    have hxrho : ‖(x : ℂ) - 1‖ ≤ rho := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx)]
      linarith
    simpa [F, G, bankPatch, hxrho] using hconj (x : ℂ) hxrho (by simp)
  · intro x hx hxR
    have hxrho : ‖(x : ℂ) - 1‖ ≤ rho := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hsign := hneg (x - 1) (by linarith) (by linarith)
    have hxid : (1 : ℂ) + ((x - 1 : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
    rw [hxid] at hsign
    simpa [F, bankPatch, hxrho] using hsign

end D5.S3.AnalyticClosure.Polylogarithm.CompositionFiniteSlit
