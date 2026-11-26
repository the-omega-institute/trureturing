/- GID: D5/S3/Analytic/Laplace/WindowEulerPole
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/WindowEulerPole
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: A first-moment Euler forcing pole obstructs an eventual exponential upper bound on a forward window. -/

import D5.S3.Analytic.Laplace.ForwardWindowLaplace
import D5.S3.Analytic.Laplace.PositiveWindowObstruction
import D5.S3.Analytic.Laplace.EulerFirstMomentLocal

/-! An Euler forcing pole obstructs a one-sided exponential bound on the forward
window of a signed first moment. -/

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace D5.S3.Analytic.Laplace.WindowEulerPole

open EulerPoleObstruction (kernel tailLaplace)
open EulerLocalContinuation (rightHalfDisk)
open ForwardWindowLaplace

/-- The Euler operator on the Laplace transform of the first moment. -/
def firstMomentEuler (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv (deriv L) z + 3 * deriv L z

/-- The source transform recovered from the window transform and the finite head. -/
private def windowQuotient (g : ℝ → ℝ) (U h : ℝ) : ℂ → ℂ :=
  (tailLaplace (forwardWindow g h) U + windowCorrection g U h) / windowMultiplier h

private theorem firstMomentEuler_analyticAt {L : ℂ → ℂ} {z : ℂ}
    (hL : AnalyticAt ℂ L z) : AnalyticAt ℂ (firstMomentEuler L) z :=
  (analyticAt_id.mul hL.deriv.deriv).add (analyticAt_const.mul hL.deriv)

private theorem firstMomentEuler_meromorphicAt {L : ℂ → ℂ} {z : ℂ}
    (hL : MeromorphicAt L z) : MeromorphicAt (firstMomentEuler L) z :=
  ((MeromorphicAt.id z).mul hL.deriv.deriv).add ((MeromorphicAt.const (3 : ℂ) z).mul hL.deriv)

private theorem windowQuotient_analyticAt {g : ℝ → ℝ} {U h : ℝ} {z : ℂ}
    (hCorrection : Differentiable ℂ (windowCorrection g U h))
    (hWindow : AnalyticAt ℂ (tailLaplace (forwardWindow g h) U) z)
    (hM : windowMultiplier h z ≠ 0) :
    AnalyticAt ℂ (windowQuotient g U h) z :=
  (hWindow.add (hCorrection.analyticAt z)).div ((windowMultiplier_entire h).analyticAt z) hM

/-- The Euler equation for the recovered source holds as an equality of meromorphic germs
throughout the open half-plane of analyticity of the window transform. -/
private theorem firstMomentEuler_windowQuotient_eventuallyEq
    {g : ℝ → ℝ} {U h c d : ℝ} {P : ℂ → ℂ}
    (hh : 0 < h) (hc : c ≤ 0) (hdc : d ≤ c)
    (hCorrection : Differentiable ℂ (windowCorrection g U h))
    (hFormula : ∀ z : ℂ, 0 < z.re → tailLaplace (forwardWindow g h) U z =
      windowMultiplier h z * tailLaplace g U z - windowCorrection g U h z)
    (hP : MeromorphicOn P {z : ℂ | d < z.re})
    (hODE : ∀ z : ℂ, 0 < z.re → firstMomentEuler (tailLaplace g U) z = P z)
    (hWindow : AnalyticOnNhd ℂ (tailLaplace (forwardWindow g h) U) {z : ℂ | c < z.re}) :
    ∀ z : ℂ, c < z.re → firstMomentEuler (windowQuotient g U h) =ᶠ[𝓝[≠] z] P := by
  have hQuotient : MeromorphicOn (windowQuotient g U h) {z : ℂ | c < z.re} := by
    intro z hz
    exact ((hWindow z hz).add (hCorrection.analyticAt z)).meromorphicAt.div
      ((windowMultiplier_entire h).analyticAt z).meromorphicAt
  have hDiff : MeromorphicOn (firstMomentEuler (windowQuotient g U h) - P)
      {z : ℂ | c < z.re} := by
    intro z hz
    exact (firstMomentEuler_meromorphicAt (hQuotient z hz)).sub (hP z (hdc.trans_lt hz))
  have hMatch (z : ℂ) (hz : 0 < z.re) :
      windowQuotient g U h =ᶠ[𝓝 z] tailLaplace g U := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with s hs
    have hM := windowMultiplier_ne_zero_of_re_ne_zero hh (ne_of_gt hs)
    change (tailLaplace (forwardWindow g h) U s + windowCorrection g U h s) /
      windowMultiplier h s = tailLaplace g U s
    apply (div_eq_iff hM).2
    rw [hFormula s hs]
    ring
  have hOne : 0 < (1 : ℂ).re := by simp
  have hInitial : (firstMomentEuler (windowQuotient g U h) - P) =ᶠ[𝓝 (1 : ℂ)] 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hOne] with s hs
    have hL := hMatch s hs
    have hEq : firstMomentEuler (windowQuotient g U h) s = P s := by
      simpa only [firstMomentEuler, hL.deriv_eq, hL.deriv.deriv_eq] using hODE s hs
    exact sub_eq_zero.mpr hEq
  have hInitialOrder :
      meromorphicOrderAt (firstMomentEuler (windowQuotient g U h) - P) 1 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (hInitial.filter_mono nhdsWithin_le_nhds)
  have hOneRight : (1 : ℂ) ∈ {z : ℂ | c < z.re} := hc.trans_lt hOne
  intro z hz
  have hOrder := hDiff.meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt c).isPreconnected hOneRight hz hInitialOrder
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hOrder] with s hs
  exact sub_eq_zero.mp hs

/-- A pole of the first-moment forcing with real part in `(σ, 0)` precludes an
eventual upper bound `C * exp (σ * t)` on the forward window. The continuation
at zero is given by a holomorphic extension of the unsmoothed source transform
on a disk, with agreement on the right half of the disk. -/
theorem no_eventually_le_exp_of_pole
    {g : ℝ → ℝ} {U h σ C : ℝ} {P : ℂ → ℂ} {a : ℂ}
    (hh : 0 < h)
    (hg : ∀ x : ℝ, 0 < x →
      IntegrableOn (fun t => Real.exp (-x * t) * g t) (Ioi U))
    (hP : MeromorphicOn P {z : ℂ | σ < z.re})
    (hPReal : ∀ c : ℝ, σ < c → c < 0 → AnalyticAt ℂ P (c : ℂ))
    (hODE : ∀ z : ℂ, 0 < z.re → firstMomentEuler (tailLaplace g U) z = P z)
    (hZero : ∃ r : ℝ, 0 < r ∧ ∃ L₀ : ℂ → ℂ,
      DifferentiableOn ℂ L₀ (ball (0 : ℂ) r) ∧
      EqOn L₀ (tailLaplace g U) (rightHalfDisk 0 r))
    (hσa : σ < a.re) (ha : a.re < 0) (hPole : meromorphicOrderAt P a < 0) :
    ¬ (∀ᶠ t : ℝ in atTop, forwardWindow g h t ≤ C * Real.exp (σ * t)) := by
  intro hBound
  have hσ : σ < 0 := hσa.trans ha
  obtain ⟨hCorrection, hLaplace⟩ := forwardWindow_laplace_halfPlane (U := U) hh hg
  have hFormula (z : ℂ) (hz : 0 < z.re) :
      tailLaplace (forwardWindow g h) U z =
        windowMultiplier h z * tailLaplace g U z - windowCorrection g U h z :=
    (hLaplace z hz).2
  have hWeighted (x : ℝ) (hx : 0 < x) :
      IntegrableOn (fun t => Real.exp (-x * t) * forwardWindow g h t) (Ioi U) := by
    have hx' : 0 < (x : ℂ).re := by simpa only [Complex.ofReal_re] using hx
    have hReal : IntegrableOn (fun t => (kernel (forwardWindow g h) (x : ℂ) t).re)
        (Ioi U) :=
      Complex.reCLM.integrable_comp (hLaplace (x : ℂ) hx').1
    have hKernel (t : ℝ) : kernel (forwardWindow g h) (x : ℂ) t =
        ((Real.exp (-x * t) * forwardWindow g h t : ℝ) : ℂ) := by
      simp only [kernel, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    simpa only [hKernel, Complex.ofReal_re] using hReal
  have hWindow : AnalyticOnNhd ℂ (tailLaplace (forwardWindow g h) U)
      {z : ℂ | σ < z.re} := by
    refine (PositiveWindowObstruction.integrable_and_analytic_of_eventually_le_exp
      hσ hWeighted hBound ?_).2
    intro c hσc hc _ hWindowRight
    rcases hc.eq_or_lt with rfl | hc
    · obtain ⟨r, hr, L₀, hL₀, hAgree⟩ := hZero
      have hExt : DifferentiableOn ℂ
          (fun z => windowMultiplier h z * L₀ z - windowCorrection g U h z)
          (ball (0 : ℂ) r) :=
        ((windowMultiplier_entire h).differentiableOn.mul hL₀).sub hCorrection.differentiableOn
      refine ⟨r, hr, fun z => windowMultiplier h z * L₀ z - windowCorrection g U h z,
        by simpa only [Complex.ofReal_zero] using hExt, ?_⟩
      intro z hz hzr
      have hzHalf : z ∈ rightHalfDisk 0 r :=
        ⟨by simpa only [Complex.ofReal_zero] using hz, hzr⟩
      change windowMultiplier h z * L₀ z - windowCorrection g U h z = _
      rw [hAgree hzHalf]
      exact (hFormula z hzr).symm
    · have hPc := hPReal c hσc hc
      have hMc : windowMultiplier h (c : ℂ) ≠ 0 :=
        windowMultiplier_ne_zero_of_re_ne_zero hh (by simpa only [Complex.ofReal_re] using hc.ne)
      have hMNear : ∀ᶠ z in 𝓝 (c : ℂ), windowMultiplier h z ≠ 0 :=
        ((windowMultiplier_entire h).analyticAt (c : ℂ)).continuousAt.tendsto
          (isOpen_compl_singleton.mem_nhds hMc)
      have hNear : {z : ℂ | AnalyticAt ℂ P z ∧ windowMultiplier h z ≠ 0} ∈ 𝓝 (c : ℂ) :=
        hPc.eventually_analyticAt.and hMNear
      obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hNear
      have hSource (z : ℂ) (hz : z ∈ rightHalfDisk c r) :
          AnalyticAt ℂ (windowQuotient g U h) z :=
        windowQuotient_analyticAt hCorrection (hWindowRight z hz.2) (hBall hz.1).2
      have hGerm := firstMomentEuler_windowQuotient_eventuallyEq (d := σ) hh hc.le
        hσc.le hCorrection hFormula hP hODE hWindowRight
      have hLocalODE (z : ℂ) (hz : z ∈ rightHalfDisk c r) :
          firstMomentEuler (windowQuotient g U h) z = P z := by
        exact tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
          ((firstMomentEuler_analyticAt (hSource z hz)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds)
          ((hBall hz.1).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (hGerm z hz.2)
      obtain ⟨δ, hδ, hδr, H, hH, hAgree⟩ := EulerFirstMomentLocal.exists_extension_of_ne_zero
        hc.ne hr (P := P) (L := windowQuotient g U h)
        (fun z hz => (hBall hz).1.differentiableAt.differentiableWithinAt)
        (fun z hz => (hSource z hz).differentiableAt.differentiableWithinAt) hLocalODE
      refine ⟨δ, hδ, fun z => windowMultiplier h z * H z - windowCorrection g U h z,
        ((windowMultiplier_entire h).differentiableOn.mul hH).sub hCorrection.differentiableOn,
        ?_⟩
      intro z hz hzr
      have hM := (hBall (ball_subset_ball hδr.le hz)).2
      change windowMultiplier h z * H z - windowCorrection g U h z = _
      rw [hAgree (show z ∈ rightHalfDisk c δ from ⟨hz, hzr⟩)]
      change windowMultiplier h z *
        ((tailLaplace (forwardWindow g h) U z + windowCorrection g U h z) /
          windowMultiplier h z) - windowCorrection g U h z = _
      rw [mul_comm (windowMultiplier h z), div_mul_cancel₀ _ hM, add_sub_cancel_right]
  have hGerm := firstMomentEuler_windowQuotient_eventuallyEq (d := σ) hh hσ.le le_rfl
    hCorrection hFormula hP hODE hWindow a hσa
  have hSource := windowQuotient_analyticAt hCorrection (hWindow a hσa)
    (windowMultiplier_ne_zero_of_re_ne_zero hh ha.ne)
  have hNonneg : 0 ≤ meromorphicOrderAt P a := by
    rw [← meromorphicOrderAt_congr hGerm]
    exact (firstMomentEuler_analyticAt hSource).meromorphicOrderAt_nonneg
  exact (not_lt_of_ge hNonneg) hPole

end D5.S3.Analytic.Laplace.WindowEulerPole
