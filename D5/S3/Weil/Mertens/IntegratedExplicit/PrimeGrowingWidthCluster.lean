/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthCluster
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The infinite phase window controls prime-tail extent errors and cluster values. -/

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

/-- Moving the left endpoint from 2 to `a` removes a nonnegative prefix. -/
private theorem movingMass_removed_bound {p K a B : ℝ} (ha : 2 ≤ a) (haB : a ≤ B)
    (hprefix : (∫ x in (2 : ℝ)..a, integrand x) ≤ K * a ^ p) :
    0 ≤ movingMass p (fun _ => 2) B - movingMass p (fun _ => a) B ∧
    movingMass p (fun _ => 2) B - movingMass p (fun _ => a) B ≤ K * (a / B) ^ p := by
  have ha₀ : 0 < a := (by norm_num : (0 : ℝ) < 2).trans_le ha
  have hB := ha₀.trans_le haB
  have hBp : 0 ≤ B ^ p := Real.rpow_nonneg hB.le _
  unfold movingMass
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (integrand_intervalIntegrable le_rfl ha) (integrand_intervalIntegrable ha haB),
    add_div, add_sub_cancel_right, Real.div_rpow ha₀.le hB.le, ← mul_div_assoc]
  exact ⟨div_nonneg (intervalIntegral.integral_nonneg_of_forall ha integrand_nonneg) hBp,
    div_le_div_of_nonneg_right hprefix hBp⟩

/-- Integrating the late power bound and absorbing the fixed early mass gives a
single bound for all prefixes, including those ending below the late threshold. -/
private theorem prefix_mass_bound {p C X : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hX : 2 ≤ X) (hdom : ∀ x ≥ X, integrand x ≤ C * x ^ (p - 1)) :
    ∃ K ≥ 0, ∀ a ≥ 2, (∫ x in (2 : ℝ)..a, integrand x) ≤ K * a ^ p := by
  let early := ∫ x in (2 : ℝ)..X, integrand x
  have hearly : 0 ≤ early := intervalIntegral.integral_nonneg_of_forall hX integrand_nonneg
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨early / (2 : ℝ) ^ p + C / p, add_nonneg (div_nonneg hearly htwo.le)
    (div_nonneg hC hp.le), fun a ha => ?_⟩
  have ha₀ : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 2).trans ha
  have habsorb : early ≤ early / (2 : ℝ) ^ p * a ^ p := by
    calc
      early = early / (2 : ℝ) ^ p * (2 : ℝ) ^ p := (div_mul_cancel₀ _ htwo.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by norm_num) ha hp.le) (div_nonneg hearly htwo.le)
  have hlate_nonneg : 0 ≤ C / p * a ^ p :=
    mul_nonneg (div_nonneg hC hp.le) (Real.rpow_nonneg ha₀ _)
  rw [add_mul]
  rcases le_total a X with haX | hXa
  · have hsmall : (∫ x in (2 : ℝ)..a, integrand x) ≤ early :=
      intervalIntegral.integral_mono_interval le_rfl ha haX
        (Eventually.of_forall integrand_nonneg) (integrand_intervalIntegrable le_rfl hX)
    linarith only [hsmall, habsorb, hlate_nonneg]
  · have hpint : -1 < p - 1 := by linarith only [hp]
    have hlate : (∫ x in X..a, integrand x) ≤ C / p * a ^ p := by
      calc
        _ ≤ ∫ x in X..a, C * x ^ (p - 1) :=
          intervalIntegral.integral_mono_on hXa (integrand_intervalIntegrable hX hXa)
            ((intervalIntegral.intervalIntegrable_rpow' hpint).const_mul _)
            (fun x hx => hdom x hx.1)
        _ = C / p * (a ^ p - X ^ p) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hpint), sub_add_cancel]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (sub_le_self _ (Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans hX) _))
          (div_nonneg hC hp.le)
    rw [← intervalIntegral.integral_add_adjacent_intervals (integrand_intervalIntegrable le_rfl hX)
      (integrand_intervalIntegrable hX hXa)]
    exact add_le_add habsorb hlate

private theorem cumulativeMass_approx {β K : ℝ} (hβ : 1 / 2 < β)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ β)
    (hprefix : ∀ a ≥ 2, (∫ x in (2 : ℝ)..a, integrand x) ≤ K * a ^ (β - 1 / 2)) :
    Tendsto (fun B => movingMass (β - 1 / 2) (fun _ => 2) B -
      phaseWindowInfinite Complex.re β (phaseOrbit (Real.log B))) atTop (𝓝 0) := by
  let p := β - 1 / 2
  have hp : 0 < p := sub_pos.mpr hβ
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε₃ : 0 < ε / 3 := by positivity
  obtain ⟨L, hL, harith, hphase⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (((exp_decay p hp K).eventually_lt_const hε₃).and
      ((exp_decay p hp (coeffMass / p)).eventually_lt_const hε₃))).exists
  let D (B : ℝ) := B * Real.exp (-L)
  have hleft : Tendsto D atTop atTop := tendsto_id.atTop_mul_const (Real.exp_pos _)
  have hfixed := (window_transfer hL (signedInput_approx (by linarith only [hβ]) hβ
    (fun k => hmax _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)))).comp
      Real.tendsto_log_atTop
  have hfixed' : Tendsto (fun B => movingMass p (fun _ => D B) B -
      phaseWindow Complex.re β L (phaseOrbit (Real.log B))) atTop (𝓝 0) := by
    refine hfixed.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    simp only [Function.comp_def, Real.exp_log hB, movingMass, D, integrand, p]
  filter_upwards [eventually_gt_atTop (0 : ℝ), hleft.eventually_ge_atTop 2,
    Metric.tendsto_nhds.mp hfixed' (ε / 3) hε₃] with B hB hD hwindow
  have hDB : D B ≤ B := mul_le_of_le_one_right hB.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL))
  have hDpow : (D B / B) ^ p = Real.exp (-p * L) := by
    dsimp only [D]
    rw [mul_div_cancel_left₀ _ hB.ne', ← Real.exp_mul]
    congr 1
    ring
  have hsegment :
      |movingMass p (fun _ => 2) B - movingMass p (fun _ => D B) B| ≤
        K * Real.exp (-p * L) := by
    have hremoved := movingMass_removed_bound hD hDB (hprefix _ hD)
    rw [abs_of_nonneg hremoved.1, ← hDpow]
    exact hremoved.2
  rw [Real.dist_eq, sub_zero] at hwindow ⊢
  let h := phaseOrbit (Real.log B)
  have htail := phaseWindowInfinite_sub_window hβ L h
  change |movingMass p (fun _ => 2) B - phaseWindowInfinite Complex.re β h| < ε
  calc
    _ ≤ |movingMass p (fun _ => 2) B - movingMass p (fun _ => D B) B| +
        |movingMass p (fun _ => D B) B - phaseWindow Complex.re β L h| +
        |phaseWindow Complex.re β L h - phaseWindowInfinite Complex.re β h| := by
      exact (abs_sub_le _ (phaseWindow Complex.re β L h) _).trans
        (add_le_add_left (abs_sub_le _ _ _) _)
    _ < ε := by
      rw [abs_sub_comm (phaseWindow Complex.re β L h), abs_of_nonneg htail.1]
      linarith only [hsegment, harith, hwindow, htail.2, hphase]

/-- Uniform control of the normalized window for every left endpoint at a common
right endpoint. The omitted prefix contributes only to the lower error. -/
theorem prime_tail_window_extent_bound_of_upper_bound (β : ℝ) :
    let realPart := Complex.re
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    ∃ K ≥ 0, ∀ ε > 0, ∀ᶠ B : ℝ in atTop, ∀ a ∈ Icc 2 B,
      let p := β - 1 / 2
      let error := (∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ p -
        phaseWindowInfinite realPart β (phaseOrbit (Real.log B))
      |error| ≤ ε + K * (a / B) ^ p ∧ error ≤ ε := by
  dsimp only
  intro hβ hmax
  let p := β - 1 / 2
  have hp : 0 < p := sub_pos.mpr hβ
  obtain ⟨C, hC, hbound⟩ := eventually_abs_normalized_tail_le hβ hmax
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hbound
  let X := max 2 X₀
  have hX : 2 ≤ X := le_max_left _ _
  have hdom (x : ℝ) (hx : X ≤ x) : integrand x ≤ C * x ^ (p - 1) :=
    integrand_le_power hC.le ((by norm_num : (0 : ℝ) < 2).trans_le (hX.trans hx))
      (hX₀ x ((le_max_right _ _).trans hx))
  obtain ⟨K, hK, hprefix⟩ := prefix_mass_bound hp hC.le hX hdom
  refine ⟨K, hK, fun ε hε => ?_⟩
  have hcumulative := Metric.tendsto_nhds.mp (cumulativeMass_approx hβ hmax hprefix) ε hε
  filter_upwards [hcumulative] with B hc a ha
  rw [Real.dist_eq, sub_zero] at hc
  have hremoved := movingMass_removed_bound ha.1 ha.2 (hprefix a ha.1)
  let w := phaseWindowInfinite Complex.re β (phaseOrbit (Real.log B))
  change |movingMass p (fun _ => a) B - w| ≤ ε + K * (a / B) ^ p ∧
    movingMass p (fun _ => a) B - w ≤ ε
  rcases abs_lt.mp hc with ⟨hlower, hupper⟩
  have hup : movingMass p (fun _ => a) B - w ≤ ε := by
    linarith only [hupper, hremoved.1]
  exact ⟨abs_le.mpr ⟨by linarith only [hlower, hremoved.2],
    hup.trans (le_add_of_nonneg_right (hremoved.1.trans hremoved.2))⟩, hup⟩

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
  let p := β - 1 / 2
  have hp : 0 < p := sub_pos.mpr hβ
  obtain ⟨K, _, hbound⟩ := prime_tail_window_extent_bound_of_upper_bound β hβ hmax
  have hdecay : Tendsto (fun B => K * (A B / B) ^ p) atTop (𝓝 0) := by
    refine ((exp_decay p hp K).comp hgrow).congr' ?_
    filter_upwards [hA] with B hAB
    have ha : 0 < A B := (by norm_num : (0 : ℝ) < 2).trans_le hAB.1
    have hb := ha.trans_le hAB.2
    have hratio : 0 < A B / B := div_pos ha hb
    change K * Real.exp (-p * Real.log (B / A B)) = K * (A B / B) ^ p
    have hlog : Real.log (A B / B) = -Real.log (B / A B) := by
      rw [← Real.log_inv, inv_div]
    rw [Real.rpow_def_of_pos hratio, hlog]
    congr 2
    ring
  have happrox : Tendsto (fun B => movingMass p A B - window (phaseOrbit (Real.log B)))
      atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    have hhalf : 0 < ε / 2 := by positivity
    filter_upwards [hA, hbound (ε / 2) hhalf, hdecay.eventually_lt_const hhalf] with B hab h hsmall
    rw [Real.dist_eq, sub_zero]
    have hb := (h (A B) hab).1
    change |movingMass p A B - window (phaseOrbit (Real.log B))| ≤ ε / 2 + K * (A B / B) ^ p at hb
    linarith only [hb, hsmall]
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
