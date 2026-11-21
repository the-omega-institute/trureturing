/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The infinite phase window gives the prime-tail mass cluster set at growing widths. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth

/-! Growing logarithmic prime-tail windows converge to the infinite phase window
evaluated along the simultaneous phase orbit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster

open PrimePhaseCluster
open PrimeAttainedCriticalWidth
  (integrand integrand_nonneg integrand_intervalIntegrable eventually_abs_normalized_tail_le
    integrand_le_power)
open PrimeOnlyTailCorrection (primeTail)

private def phaseDensity (realPart : ℂ → ℝ) (β : ℝ) (h : ℕ → Circle) (s : ℝ) : ℝ :=
  Real.exp (-(β - 1 / 2) * s) * max (-phaseProfile realPart β h (-s)) 0

/-- The exponentially weighted negative part of the phase profile over positive lags. -/
def phaseWindowInfinite (realPart : ℂ → ℝ) (β : ℝ) (h : ℕ → Circle) : ℝ :=
  ∫ s in Ioi (0 : ℝ), phaseDensity realPart β h s ∂volume

private def coeffMass : ℝ := ∑' k : ℕ, ‖actualCoeff k‖

private theorem phaseDensity_bound (realPart : ℂ → ℝ) (β : ℝ) (h : ℕ → Circle) (s : ℝ) :
    0 ≤ phaseDensity realPart β h s ∧
    phaseDensity realPart β h s ≤ coeffMass * Real.exp (-(β - 1 / 2) * s) := by
  let term (k : ℕ) := rightmostCoeff realPart β k * (h k : ℂ) * (phaseOrbit (-s) k : ℂ)
  have hcoeff := actualCoeff_hasSum.summable.norm
  have hterm (k : ℕ) : ‖term k‖ ≤ ‖actualCoeff k‖ := by
    simp only [term, norm_mul, Circle.norm_coe, mul_one, rightmostCoeff]
    split_ifs
    · rfl
    · exact norm_zero.trans_le (norm_nonneg _)
  have hs := Summable.of_nonneg_of_le (fun k => norm_nonneg (term k)) hterm hcoeff
  have hprofile : -phaseProfile realPart β h (-s) ≤ coeffMass := by
    rw [phaseProfile, neg_neg]
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
      ((norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hterm hcoeff)))
  refine ⟨mul_nonneg (Real.exp_nonneg _) (le_max_right _ _), ?_⟩
  rw [phaseDensity, mul_comm coeffMass]
  exact mul_le_mul_of_nonneg_left
    (max_le hprofile (tsum_nonneg fun _ => norm_nonneg _)) (Real.exp_nonneg _)

private theorem phaseDensity_continuous (realPart : ℂ → ℝ) (β : ℝ) (h : ℕ → Circle) :
    Continuous (phaseDensity realPart β h) := by
  exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(β - 1 / 2) * s)).mul
    (((phaseProfile_continuous realPart β).comp
      (continuous_const.prodMk continuous_neg)).neg.max continuous_const)

private theorem phaseWindowInfinite_sub_window {β : ℝ} (hβ : 1 / 2 < β)
    (L : ℝ) (h : ℕ → Circle) :
    0 ≤ phaseWindowInfinite Complex.re β h - phaseWindow Complex.re β L h ∧
    phaseWindowInfinite Complex.re β h - phaseWindow Complex.re β L h ≤
      coeffMass / (β - 1 / 2) * Real.exp (-(β - 1 / 2) * L) := by
  let p := β - 1 / 2
  let f := phaseDensity Complex.re β h
  have hp : 0 < p := sub_pos.mpr hβ
  have hmajor (a : ℝ) : IntegrableOn (fun s : ℝ => coeffMass * Real.exp (-p * s)) (Ioi a) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hp) a).const_mul _
  have hint (a : ℝ) : IntegrableOn f (Ioi a) :=
    (hmajor a).mono' (phaseDensity_continuous Complex.re β h).aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (phaseDensity_bound Complex.re β h s).1]
        exact (phaseDensity_bound Complex.re β h s).2)
  change 0 ≤ (∫ s in Ioi 0, f s) - (∫ s in 0..L, f s) ∧
    (∫ s in Ioi 0, f s) - (∫ s in 0..L, f s) ≤ _
  rw [← intervalIntegral.integral_interval_add_Ioi (hint 0) (hint L), add_sub_cancel_left]
  refine ⟨integral_nonneg fun s => (phaseDensity_bound Complex.re β h s).1, ?_⟩
  calc
    _ ≤ ∫ s in Ioi L, coeffMass * Real.exp (-p * s) :=
      setIntegral_mono_on (hint L) (hmajor L) measurableSet_Ioi
        (fun s _ => (phaseDensity_bound Complex.re β h s).2)
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hp), neg_div_neg_eq]
      change coeffMass * (Real.exp (-p * L) / p) = coeffMass / p * Real.exp (-p * L)
      ring

private theorem exp_decay (p : ℝ) (hp : 0 < p) (c : ℝ) :
    Tendsto (fun L : ℝ => c * Real.exp (-p * L)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)).const_mul c

private theorem phaseWindow_tendstoUniformly {β : ℝ} (hβ : 1 / 2 < β) :
    TendstoUniformly (phaseWindow Complex.re β) (phaseWindowInfinite Complex.re β) atTop := by
  refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
  have hdecay := exp_decay (β - 1 / 2) (sub_pos.mpr hβ) (coeffMass / (β - 1 / 2))
  filter_upwards [hdecay.eventually_lt_const hε] with L hsmall h
  have htail := phaseWindowInfinite_sub_window hβ L h
  rw [Real.dist_eq, abs_of_nonneg htail.1]
  exact htail.2.trans_lt hsmall

private def movingMass (p : ℝ) (A : ℝ → ℝ) (B : ℝ) : ℝ :=
  (∫ x in A B..B, integrand x) / B ^ p

private def fixedLeft (L B : ℝ) : ℝ := B * Real.exp (-L)

/-- The exterior mass is bounded by a fixed early integral and the late power integral,
uniformly in the choice of admissible left endpoint. -/
private theorem eventually_exterior_mass_bound {p C X : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hX : 2 ≤ X) (hdom : ∀ x ≥ X, integrand x ≤ C * x ^ (p - 1))
    {A : ℝ → ℝ} (hA : ∀ᶠ B in atTop, 2 ≤ A B ∧ A B ≤ B)
    (hgrow : Tendsto (fun B => Real.log (B / A B)) atTop atTop)
    {L : ℝ} (hL : 0 ≤ L) :
    ∀ᶠ B in atTop,
      0 ≤ movingMass p A B - movingMass p (fixedLeft L) B ∧
      movingMass p A B - movingMass p (fixedLeft L) B ≤
        C / p * Real.exp (-p * L) + (∫ x in (2 : ℝ)..X, integrand x) / B ^ p := by
  have hleft : Tendsto (fixedLeft L) atTop atTop :=
    tendsto_id.atTop_mul_const (Real.exp_pos _)
  filter_upwards [hA, hgrow.eventually_ge_atTop L, hleft.eventually_ge_atTop X] with B hAB hlog hXD
  let D := fixedLeft L B
  have hA₀ : 0 < A B := (by norm_num : (0 : ℝ) < 2).trans_le hAB.1
  have hB₀ : 0 < B := hA₀.trans_le hAB.2
  have hAD : A B ≤ D := by
    have hquot := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (div_pos hB₀ hA₀)] at hquot
    have hmul := (le_div_iff₀ hA₀).mp hquot
    change A B ≤ B * Real.exp (-L)
    simpa only [Real.exp_neg, div_eq_mul_inv] using
      (le_div_iff₀ (Real.exp_pos L)).mpr (by rwa [mul_comm])
  have hDB : D ≤ B := mul_le_of_le_one_right hB₀.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL))
  have hBp : 0 < B ^ p := Real.rpow_pos_of_pos hB₀ _
  have hadd :
      movingMass p A B - movingMass p (fixedLeft L) B = (∫ x in A B..D, integrand x) / B ^ p := by
    change (∫ x in A B..B, integrand x) / B ^ p - (∫ x in D..B, integrand x) / B ^ p = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (integrand_intervalIntegrable hAB.1 hAD) (integrand_intervalIntegrable (hX.trans hXD) hDB),
      add_div, add_sub_cancel_right]
  let M := max (A B) X
  have hAM : A B ≤ M := le_max_left _ _
  have hXM : X ≤ M := le_max_right _ _
  have hMD : M ≤ D := max_le hAD hXD
  have hearly : (∫ x in A B..M, integrand x) ≤ ∫ x in (2 : ℝ)..X, integrand x := by
    rcases le_total (A B) X with h | h
    · rw [show M = X from max_eq_right h]
      exact intervalIntegral.integral_mono_interval hAB.1 h le_rfl
        (Eventually.of_forall integrand_nonneg) (integrand_intervalIntegrable le_rfl hX)
    · rw [show M = A B from max_eq_left h, intervalIntegral.integral_same]
      exact intervalIntegral.integral_nonneg_of_forall hX integrand_nonneg
  have hpint : -1 < p - 1 := by linarith only [hp]
  have hDpow : D ^ p = B ^ p * Real.exp (-p * L) := by
    change (B * Real.exp (-L)) ^ p = _
    rw [Real.mul_rpow hB₀.le (Real.exp_nonneg _), ← Real.exp_mul]
    congr 2
    ring
  have hlate : (∫ x in M..D, integrand x) ≤ C / p * D ^ p := by
    calc
      _ ≤ ∫ x in M..D, C * x ^ (p - 1) :=
        intervalIntegral.integral_mono_on hMD
          (integrand_intervalIntegrable (hX.trans hXM) hMD)
          ((intervalIntegral.intervalIntegrable_rpow' hpint).const_mul _)
          (fun x hx => hdom x (hXM.trans hx.1))
      _ = C / p * (D ^ p - M ^ p) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hpint), sub_add_cancel]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans (hX.trans hXM)) _))
        (div_nonneg hC hp.le)
  rw [hadd]
  refine ⟨div_nonneg (intervalIntegral.integral_nonneg_of_forall hAD integrand_nonneg) hBp.le, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (integrand_intervalIntegrable hAB.1 hAM)
    (integrand_intervalIntegrable (hX.trans hXM) hMD)]
  calc
    _ ≤ ((∫ x in (2 : ℝ)..X, integrand x) + C / p * D ^ p) / B ^ p :=
      div_le_div_of_nonneg_right (add_le_add hearly hlate) hBp.le
    _ = _ := by rw [hDpow, add_div]; field_simp; ring

private theorem movingMass_approx {β : ℝ} (hβ : 1 / 2 < β)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ β)
    {A : ℝ → ℝ} (hA : ∀ᶠ B in atTop, 2 ≤ A B ∧ A B ≤ B)
    (hgrow : Tendsto (fun B => Real.log (B / A B)) atTop atTop) :
    Tendsto (fun B => movingMass (β - 1 / 2) A B -
      phaseWindowInfinite Complex.re β (phaseOrbit (Real.log B))) atTop (𝓝 0) := by
  let p := β - 1 / 2
  have hp : 0 < p := sub_pos.mpr hβ
  obtain ⟨C, hC, hbound⟩ := eventually_abs_normalized_tail_le hβ hmax
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hbound
  let X := max 2 X₀
  have hX : 2 ≤ X := le_max_left _ _
  have hdom (x : ℝ) (hx : X ≤ x) : integrand x ≤ C * x ^ (p - 1) :=
    integrand_le_power hC.le ((by norm_num : (0 : ℝ) < 2).trans_le (hX.trans hx))
      (hX₀ x ((le_max_right _ _).trans hx))
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε₄ : 0 < ε / 4 := by positivity
  obtain ⟨L, hL, harith, hphase⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (((exp_decay p hp (C / p)).eventually_lt_const hε₄).and
      ((exp_decay p hp (coeffMass / p)).eventually_lt_const hε₄))).exists
  have hfixed := (window_transfer hL (signedInput_approx (by linarith only [hβ]) hβ
    (fun k => hmax _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)))).comp
      Real.tendsto_log_atTop
  have hfixed' : Tendsto (fun B => movingMass p (fixedLeft L) B -
      phaseWindow Complex.re β L (phaseOrbit (Real.log B))) atTop (𝓝 0) := by
    refine hfixed.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    simp only [Function.comp_def, Real.exp_log hB, movingMass, fixedLeft, integrand, p]
  have hearly : Tendsto (fun B : ℝ => (∫ x in (2 : ℝ)..X, integrand x) / B ^ p)
      atTop (𝓝 0) := (tendsto_rpow_atTop hp).const_div_atTop _
  filter_upwards [eventually_exterior_mass_bound hp hC.le hX hdom hA hgrow hL,
    hearly.eventually_lt_const hε₄, Metric.tendsto_nhds.mp hfixed' (ε / 4) hε₄] with
      B hsegment he hwindow
  rw [Real.dist_eq, sub_zero] at hwindow ⊢
  let h := phaseOrbit (Real.log B)
  have htail := phaseWindowInfinite_sub_window hβ L h
  change |movingMass p A B - phaseWindowInfinite Complex.re β h| < ε
  calc
    _ ≤ |movingMass p A B - movingMass p (fixedLeft L) B| +
        |movingMass p (fixedLeft L) B - phaseWindow Complex.re β L h| +
        |phaseWindow Complex.re β L h - phaseWindowInfinite Complex.re β h| := by
      exact (abs_sub_le _ (phaseWindow Complex.re β L h) _).trans
        (add_le_add_left (abs_sub_le _ _ _) _)
    _ < ε := by
      rw [abs_of_nonneg hsegment.1, abs_sub_comm (phaseWindow Complex.re β L h),
        abs_of_nonneg htail.1]
      linarith only [hsegment.2, he, harith, hwindow, htail.2, hphase]

/-- At any real-part upper bound above one half, every admissible growing logarithmic
window has exactly the cluster values of the infinite integral on the actual phase hull. -/
theorem prime_tail_growing_width_cluster_iff_of_upper_bound (β : ℝ) :
    let realPart := Complex.re
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    ∀ (A : ℝ → ℝ), (∀ᶠ B in atTop, 2 ≤ A B ∧ A B ≤ B) →
      Tendsto (fun B => Real.log (B / A B)) atTop atTop → ∀ y : ℝ,
        MapClusterPt y atTop (fun B : ℝ =>
          (∫ x in A B..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (β - 1 / 2)) ↔
        ∃ h ∈ closure (range phaseOrbit), y = phaseWindowInfinite realPart β h := by
  dsimp only
  intro hβ hmax A hA hgrow y
  let window := phaseWindowInfinite Complex.re β
  have hcontinuous : Continuous window :=
    (phaseWindow_tendstoUniformly hβ).continuous
      (Frequently.of_forall (phaseWindow_continuous β))
  have happrox := movingMass_approx hβ hmax hA hgrow
  have himage : IsClosed (window '' closure (range phaseOrbit)) :=
    (isClosed_closure.isCompact.image hcontinuous).isClosed
  change MapClusterPt y atTop (movingMass (β - 1 / 2) A) ↔ _
  constructor
  · intro hy
    have hm := himage.mem_of_mapClusterPt (mapClusterPt_of_sub_tendsto_zero happrox hy)
      (Eventually.of_forall fun B =>
        mem_image_of_mem window (subset_closure (mem_range_self (Real.log B))))
    obtain ⟨h, hh, hval⟩ := hm
    exact ⟨h, hh, hval.symm⟩
  · rintro ⟨h, hh, rfl⟩
    have hc := ((phaseOrbit_cluster_iff h).mpr hh).continuousAt_comp hcontinuous.continuousAt
    have hlog : MapClusterPt (window h) atTop (window ∘ phaseOrbit ∘ Real.log) := by
      apply MapClusterPt.of_comp Real.tendsto_exp_atTop
      apply hc.congrFun
      exact Eventually.of_forall fun t => by simp only [Function.comp_def, Real.log_exp]
    exact mapClusterPt_of_sub_tendsto_zero
      (by simpa only [window, Function.comp_def, neg_sub, neg_zero] using happrox.neg) hlog

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeGrowingWidthCluster
