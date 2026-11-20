/- GID: D5/S3/Analytic/Laplace/ForwardWindowLaplace
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/ForwardWindowLaplace
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: A forward window multiplies the tail Laplace transform and subtracts an entire cutoff correction under local integrability. -/

import D5.S3.Analytic.Laplace.EulerPoleObstruction
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! The Laplace multiplier and the finite cutoff correction for a forward box. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace D5.S3.Analytic.Laplace.ForwardWindowLaplace

open EulerPoleObstruction (kernel tailLaplace finiteHead finiteHead_entire euler)

/-- The forward box integral. For nonnegative width this is the integral from 0 to h. -/
def forwardWindow (g : ℝ → ℝ) (h t : ℝ) : ℝ :=
  ∫ v in Ioc 0 h, g (t + v)

theorem forwardWindow_eq_intervalIntegral (g : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    forwardWindow g h t = ∫ v in (0 : ℝ)..h, g (t + v) :=
  (intervalIntegral.integral_of_le hh).symm

/-- The positive exponent comes from translating the Laplace kernel forward. -/
def windowMultiplier (h : ℝ) (z : ℂ) : ℂ :=
  ∫ v in Ioc 0 h, Complex.exp (z * (v : ℂ))

/-- The box integral accumulated on the finite interval immediately below the cutoff
after extending the source by zero on the left. This term is subtracted. -/
def windowCorrection (g : ℝ → ℝ) (U h : ℝ) (z : ℂ) : ℂ :=
  finiteHead (fun t => ∫ u in Ioc U (t + h), g u) (U - h) U z

theorem windowMultiplier_entire (h : ℝ) : Differentiable ℂ (windowMultiplier h) := by
  have hd : Differentiable ℂ (finiteHead (fun _ : ℝ => (1 : ℝ)) 0 h) :=
    finiteHead_entire continuous_const.integrableOn_Ioc
  simpa only [Function.comp_def, finiteHead, kernel, neg_neg, Complex.ofReal_one, mul_one,
    windowMultiplier] using! hd.comp (differentiable_neg : Differentiable ℂ (Neg.neg : ℂ → ℂ))

theorem windowMultiplier_eq_div {h : ℝ} (hh : 0 ≤ h) {z : ℂ} (hz : z ≠ 0) :
    windowMultiplier h z = (Complex.exp (z * (h : ℂ)) - 1) / z := by
  rw [windowMultiplier, ← intervalIntegral.integral_of_le hh, integral_exp_mul_complex hz]
  simp

theorem windowMultiplier_ne_zero_of_re_ne_zero {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : z.re ≠ 0) : windowMultiplier h z ≠ 0 := by
  have hz₀ : z ≠ 0 := by
    intro he
    exact hz (by simp [he])
  rw [windowMultiplier_eq_div hh.le hz₀]
  refine div_ne_zero (sub_ne_zero.mpr ?_) hz₀
  intro he
  have hn := congrArg (fun w : ℂ => ‖w‖) he
  have hreal : Real.exp (z.re * h) = 1 := by
    simpa only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, norm_one] using hn
  exact (mul_ne_zero hz hh.ne') ((Real.exp_eq_one_iff (z.re * h)).mp hreal)

/-- Absolute Fubini follows by pulling back an integrable product along
the measure-preserving translation (t, v) ↦ (t + v, v). -/
private theorem integrate_window {𝕜 : Type*} [RCLike 𝕜] {f w : ℝ → 𝕜} {h : ℝ}
    (hf : Integrable f) (hw : IntegrableOn w (Ioc 0 h)) :
    Integrable (fun t => ∫ v in Ioc 0 h, f (t + v) * w v) ∧
      (∫ t : ℝ, ∫ v in Ioc 0 h, f (t + v) * w v) =
        (∫ t, f t) * ∫ v in Ioc 0 h, w v := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 h)
  have hp : Integrable (fun p : ℝ × ℝ => f (p.1 + p.2) * w p.2)
      ((volume : Measure ℝ).prod ν) :=
    (measurePreserving_add_prod volume ν).integrable_comp_of_integrable
      (hf.mul_prod (show Integrable w ν from hw))
  refine ⟨hp.integral_prod_left, ?_⟩
  calc
    _ = ∫ v in Ioc 0 h, ∫ t : ℝ, f (t + v) * w v :=
      integral_integral_swap (f := fun t v => f (t + v) * w v) hp
    _ = _ := by
      simp_rw [integral_mul_const, integral_add_right_eq_self, integral_const_mul]

private theorem cutoff_window_on_head (g : ℝ → ℝ) {U h t : ℝ}
    (hh : 0 ≤ h) (ht : t ≤ U) :
    forwardWindow ((Ioi U).indicator g) h t = ∫ u in Ioc U (t + h), g u := by
  have hshift : t ≤ t + h := by linarith
  have hs : Ioi U ∩ Ioc t (t + h) = Ioc U (t + h) := by
    ext u
    change (U < u ∧ t < u ∧ u ≤ t + h) ↔ (U < u ∧ u ≤ t + h)
    exact ⟨fun hu => ⟨hu.1, hu.2.2⟩, fun hu => ⟨hu.1, ht.trans_lt hu.1, hu.2⟩⟩
  rw [forwardWindow, ← intervalIntegral.integral_of_le hh,
    intervalIntegral.integral_comp_add_left, add_zero, intervalIntegral.integral_of_le hshift,
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hs]

theorem windowCorrection_entire {g : ℝ → ℝ} {U h : ℝ} (hh : 0 ≤ h)
    (hg : IntegrableOn g (Ioc U (U + h))) : Differentiable ℂ (windowCorrection g U h) := by
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 h) :=
    continuous_const.integrableOn_Ioc
  have hi : Integrable (forwardWindow ((Ioc U (U + h)).indicator g) h) := by
    simpa only [forwardWindow, mul_one] using!
      (integrate_window (hg.integrable_indicator measurableSet_Ioc) hone).1
  unfold windowCorrection
  apply finiteHead_entire
  refine hi.integrableOn.congr_fun ?_ measurableSet_Ioc
  intro t ht
  calc
    _ = forwardWindow ((Ioi U).indicator g) h t := by
      unfold forwardWindow
      apply setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      have huv : t + v ≤ U + h := add_le_add ht.2 hv.2
      simp only [indicator_apply, mem_Ioc, mem_Ioi, huv, and_true]
    _ = _ := cutoff_window_on_head g hh ht.2

private theorem unweight (x u y : ℝ) :
    Real.exp (x * u) * (Real.exp (-x * u) * y) = y := by
  rw [← mul_assoc, ← Real.exp_add, show x * u + -x * u = 0 by ring, Real.exp_zero, one_mul]

/-- A single real exponential weight controls the absolute integral at a complex
parameter with that real part. -/
theorem kernel_integrable_of_real_weight {g : ℝ → ℝ} {U : ℝ} {z : ℂ}
    (hg : IntegrableOn (fun u => Real.exp (-z.re * u) * g u) (Ioi U)) :
    IntegrableOn (kernel g z) (Ioi U) := by
  have he : Continuous (fun u : ℝ => Real.exp (z.re * u)) := by fun_prop
  have hm : AEStronglyMeasurable g (volume.restrict (Ioi U)) := by
    have hm' : AEStronglyMeasurable
        (fun u => Real.exp (z.re * u) * (Real.exp (-z.re * u) * g u))
        (volume.restrict (Ioi U)) :=
      he.aestronglyMeasurable.mul hg.aestronglyMeasurable
    simpa only [unweight] using hm'
  have hk : Continuous (fun u : ℝ => Complex.exp (-z * (u : ℂ))) := by fun_prop
  refine hg.norm.mono'
    (hk.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)) ?_
  filter_upwards with u
  change ‖kernel g z u‖ ≤ ‖Real.exp (-z.re * u) * g u‖
  simp [kernel, norm_mul, Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

private theorem head_integrable_of_real_weight {g : ℝ → ℝ} {U V x : ℝ}
    (hg : IntegrableOn (fun u => Real.exp (-x * u) * g u) (Ioi U)) :
    IntegrableOn g (Ioc U V) := by
  have he : Continuous (fun u : ℝ => Real.exp (x * u)) := by fun_prop
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc U V)).exists_bound_of_continuousOn
    he.continuousOn
  have hb : ∀ᵐ u ∂volume.restrict (Ioc U V), ‖Real.exp (x * u)‖ ≤ K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hK u ⟨hu.1.le, hu.2⟩
  simpa only [IntegrableOn, unweight] using!
    (hg.mono_set (Ioc_subset_Ioi_self : Ioc U V ⊆ Ioi U)).bdd_mul
      he.aestronglyMeasurable hb

/-- The actual window kernel is integrable whenever the actual source kernel is.
The part of the translated source below the original cutoff is the finite head. -/
theorem tailLaplace_forwardWindow {g : ℝ → ℝ} {U h : ℝ} (hh : 0 ≤ h) {z : ℂ}
    (hg : IntegrableOn (kernel g z) (Ioi U)) :
    IntegrableOn (kernel (forwardWindow g h) z) (Ioi U) ∧
      tailLaplace (forwardWindow g h) U z =
        windowMultiplier h z * tailLaplace g U z - windowCorrection g U h z := by
  let g₀ := (Ioi U).indicator g
  have hk : kernel g₀ z = (Ioi U).indicator (kernel g z) := by
    funext t
    by_cases ht : t ∈ Ioi U <;> simp [g₀, kernel, ht]
  have hki : Integrable (kernel g₀ z) := by
    rw [hk]
    exact hg.integrable_indicator measurableSet_Ioi
  have hw : IntegrableOn (fun v : ℝ => Complex.exp (z * (v : ℂ))) (Ioc 0 h) :=
    (by fun_prop : Continuous (fun v : ℝ => Complex.exp (z * (v : ℂ)))).integrableOn_Ioc
  obtain ⟨hi, hprod⟩ := integrate_window hki hw
  have hsection (t : ℝ) :
      (∫ v in Ioc 0 h, kernel g₀ z (t + v) * Complex.exp (z * (v : ℂ))) =
        kernel (forwardWindow g₀ h) z t := by
    calc
      _ = ∫ v in Ioc 0 h, Complex.exp (-z * (t : ℂ)) * (g₀ (t + v) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro v _
        dsimp only [kernel]
        rw [mul_right_comm, ← Complex.exp_add]
        rw [show -z * ((t + v : ℝ) : ℂ) + z * (v : ℂ) = -z * (t : ℂ) by
          push_cast
          ring]
      _ = _ := by simp only [integral_const_mul, integral_complex_ofReal, kernel, forwardWindow]
  have hInt : Integrable (kernel (forwardWindow g₀ h) z) :=
    hi.congr (Eventually.of_forall hsection)
  have hFull : (∫ t, kernel (forwardWindow g₀ h) z t) =
      windowMultiplier h z * tailLaplace g U z := by
    rw [← integral_congr_ae (Eventually.of_forall hsection), hprod, hk,
      integral_indicator measurableSet_Ioi]
    exact mul_comm _ _
  have hsupp (t : ℝ) (ht : t ∉ Ioi (U - h)) :
      kernel (forwardWindow g₀ h) z t = 0 := by
    have htle : t ≤ U - h := le_of_not_gt ht
    have hzero : forwardWindow g₀ h t = 0 := by
      unfold forwardWindow
      calc
        _ = ∫ v in Ioc 0 h, (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro v hv
          have hn : t + v ∉ Ioi U := by
            change ¬ U < t + v
            linarith [hv.2]
          simp [g₀, hn]
        _ = _ := by simp
    simp [kernel, hzero]
  have hsplit : (∫ t, kernel (forwardWindow g₀ h) z t) =
      (∫ t in Ioc (U - h) U, kernel (forwardWindow g₀ h) z t) +
        ∫ t in Ioi U, kernel (forwardWindow g₀ h) z t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      ← Ioc_union_Ioi_eq_Ioi (sub_le_self U hh)]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hInt.integrableOn hInt.integrableOn
  have htail : EqOn (kernel (forwardWindow g₀ h) z) (kernel (forwardWindow g h) z) (Ioi U) := by
    intro t ht
    have he : forwardWindow g₀ h t = forwardWindow g h t := by
      unfold forwardWindow
      apply setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      have hm : t + v ∈ Ioi U := by
        change U < t + v
        exact (show U < t from ht).trans (lt_add_of_pos_right t hv.1)
      simp [g₀, hm]
    simp only [kernel, he]
  have hhead : (∫ t in Ioc (U - h) U, kernel (forwardWindow g₀ h) z t) =
      windowCorrection g U h z := by
    unfold windowCorrection finiteHead
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [kernel, g₀, cutoff_window_on_head g hh ht.2]
  refine ⟨hInt.integrableOn.congr_fun htail measurableSet_Ioi, eq_sub_iff_add_eq.mpr ?_⟩
  rw [hhead, setIntegral_congr_fun measurableSet_Ioi htail] at hsplit
  exact (add_comm _ _).trans (hsplit.symm.trans hFull)

/-- Absolute convergence and the transform identity on the positive half-plane.
Local integrability at the finite head follows from any one of the real weights. -/
theorem forwardWindow_laplace_halfPlane {g : ℝ → ℝ} {U h : ℝ} (hh : 0 < h)
    (hg : ∀ x : ℝ, 0 < x → IntegrableOn (fun u => Real.exp (-x * u) * g u) (Ioi U)) :
    Differentiable ℂ (windowCorrection g U h) ∧
      ∀ z : ℂ, 0 < z.re → IntegrableOn (kernel (forwardWindow g h) z) (Ioi U) ∧
        tailLaplace (forwardWindow g h) U z =
          windowMultiplier h z * tailLaplace g U z - windowCorrection g U h z := by
  refine ⟨windowCorrection_entire hh.le (head_integrable_of_real_weight (hg 1 zero_lt_one)), ?_⟩
  intro z hz
  exact tailLaplace_forwardWindow hh.le (kernel_integrable_of_real_weight (hg z.re hz))

/-- Read the first-moment transform from the differentiated integral supplied by
the actual theta-tail Laplace theorem. -/
theorem tailLaplace_firstMoment_eq_neg_deriv {f : ℝ → ℝ} {U : ℝ} {s : ℂ}
    (hf : HasDerivAt (tailLaplace f U)
      (-(∫ t in Ioi U, (t : ℂ) * Complex.exp (-s * (t : ℂ)) * (f t : ℂ))) s) :
    tailLaplace (fun t => t * f t) U s = -deriv (tailLaplace f U) s := by
  rw [hf.deriv, neg_neg, tailLaplace]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [Complex.ofReal_mul]
  ring

/-- For the transform L of the first moment of the source, use L = -F' as a germ.
The actual theta tail supplies this germ via the first derivative in
`ActualThetaTailLaplace.actual_theta_tail_laplace_ode`.
Differentiating the equation euler F = Φ yields the window input equation. -/
theorem neg_deriv_euler_of_first_moment {F Φ L : ℂ → ℂ} {s : ℂ}
    (hF : AnalyticAt ℂ F s) (hΦ : euler F =ᶠ[𝓝 s] Φ)
    (hL : L =ᶠ[𝓝 s] -deriv F) :
    -deriv Φ s = s * deriv (deriv L) s + 3 * deriv L s := by
  have hd : HasDerivAt (euler F)
      (deriv (deriv F) s + s * deriv (deriv (deriv F)) s + 2 * deriv (deriv F) s) s := by
    simpa only [euler, Pi.add_apply, Pi.mul_apply, id_eq, one_mul] using!
      (((hasDerivAt_id s).mul hF.deriv.deriv.differentiableAt.hasDerivAt).add
        (hF.deriv.differentiableAt.hasDerivAt.const_mul (2 : ℂ)))
  have hD : deriv L =ᶠ[𝓝 s] -(deriv (deriv F)) := by
    filter_upwards [hL.deriv] with z hz
    exact hz.trans deriv.neg
  have hDD : deriv (deriv L) s = -deriv (deriv (deriv F)) s := by
    simpa only [deriv.neg] using hD.deriv_eq
  rw [← hΦ.deriv_eq, hd.deriv, hD.eq_of_nhds, hDD]
  simp only [Pi.neg_apply]
  ring

end D5.S3.Analytic.Laplace.ForwardWindowLaplace
