/- GID: D5/S3/Arith/Robin/SelectedEndpointMoment
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/SelectedEndpointMoment
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.Set]
   utility: none
   digest: Equal-mass integral minima pay lower bounds for the literal selected endpoint moment. -/

import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.SelectedEndpointMoment

/-- The comparison interval retains all mass at its lower endpoint, so this
monotone-cost minimum also applies to measures with atoms. -/
theorem monotone_window_integral_minimum
    {μ : Measure ℝ} {f : ℝ → ℝ} {l b r : ℝ} {S : Set ℝ}
    (hlb : l ≤ b) (hbr : b ≤ r) (hS : MeasurableSet S)
    (hsub : S ⊆ Icc l r) (hmono : MonotoneOn f (Icc l r))
    (hfiniteS : μ S ≠ ⊤) (hfiniteI : μ (Icc l b) ≠ ⊤)
    (hcostS : IntegrableOn f S μ) (hcostI : IntegrableOn f (Icc l b) μ)
    (hmass : μ.real S = μ.real (Icc l b)) :
    (∫ x in Icc l b, f x ∂μ) ≤ ∫ x in S, f x ∂μ := by
  classical
  have hb : b ∈ Icc l r := ⟨hlb, hbr⟩
  have hcS : IntegrableOn (fun x => f x - f b) S μ :=
    hcostS.sub (integrableOn_const hfiniteS)
  have hcI : IntegrableOn (fun x => f x - f b) (Icc l b) μ :=
    hcostI.sub (integrableOn_const hfiniteI)
  have hpoint : ∀ x : ℝ,
      (Icc l b).indicator (fun x => f x - f b) x ≤
        S.indicator (fun x => f x - f b) x := by
    intro x
    by_cases hxS : x ∈ S
    · by_cases hxI : x ∈ Icc l b
      · simp only [indicator_of_mem hxS, indicator_of_mem hxI, le_refl]
      · rw [indicator_of_mem hxS, indicator_of_notMem hxI]
        have hx : x ∈ Icc l r := hsub hxS
        have hbx : b ≤ x := by
          by_contra h
          exact hxI ⟨hx.1, (not_le.mp h).le⟩
        exact sub_nonneg.mpr (hmono hb hx hbx)
    · by_cases hxI : x ∈ Icc l b
      · rw [indicator_of_notMem hxS, indicator_of_mem hxI]
        exact sub_nonpos.mpr (hmono ⟨hxI.1, hxI.2.trans hbr⟩ hb hxI.2)
      · simp only [indicator_of_notMem hxS, indicator_of_notMem hxI, le_refl]
  have hcompare := integral_mono
    (hcI.integrable_indicator measurableSet_Icc) (hcS.integrable_indicator hS) hpoint
  rw [integral_indicator measurableSet_Icc, integral_indicator hS,
    integral_sub hcostI (integrableOn_const hfiniteI),
    integral_sub hcostS (integrableOn_const hfiniteS),
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, hmass] at hcompare
  linarith

private lemma volume_window_mass {l r : ℝ} {S : Set ℝ}
    (hlr : l ≤ r) (hsub : S ⊆ Icc l r) :
    volume.real S ≤ r - l := by
  have h := measureReal_mono (μ := volume) hsub
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  simpa only [measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hlr)] using h

private lemma continuous_window_minimum {f : ℝ → ℝ} {l r : ℝ} {S : Set ℝ}
    (hlr : l ≤ r) (hS : MeasurableSet S) (hsub : S ⊆ Icc l r)
    (hc : Continuous f) (hmono : MonotoneOn f (Icc l r)) :
    (∫ t in Icc l (l + volume.real S), f t) ≤ ∫ t in S, f t := by
  have hm : 0 ≤ volume.real S := measureReal_nonneg
  have hml := volume_window_mass hlr hsub
  have hbound : l + volume.real S ≤ r := by linarith
  have hfinite : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono hsub)
  apply monotone_window_integral_minimum (by linarith) hbound hS hsub hmono hfinite
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (hc.continuousOn.integrableOn_Icc.mono_set hsub) hc.continuousOn.integrableOn_Icc
  simp only [measureReal_def, Real.volume_Icc, add_sub_cancel_left,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

private lemma quadratic_window_lower {l r : ℝ} {S : Set ℝ}
    (hlr : l ≤ r) (hS : MeasurableSet S) (hsub : S ⊆ Icc l r) :
    volume.real S ^ 3 / 3 ≤ ∫ t in S, (t - l) ^ 2 := by
  have hc : Continuous (fun t : ℝ => (t - l) ^ 2) :=
    (continuous_id.sub continuous_const).pow 2
  have hmono : MonotoneOn (fun t : ℝ => (t - l) ^ 2) (Icc l r) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x - l := sub_nonneg.mpr hx.1
    have hy0 : 0 ≤ y - l := sub_nonneg.mpr hy.1
    exact (sq_le_sq₀ hx0 hy0).mpr (sub_le_sub_right hxy l)
  have hmin := continuous_window_minimum hlr hS hsub hc hmono
  have hm : 0 ≤ volume.real S := measureReal_nonneg
  have hi : (∫ t in Icc l (l + volume.real S), (t - l) ^ 2) =
      volume.real S ^ 3 / 3 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show l ≤ l + volume.real S by linarith)]
    have hderiv : ∀ t ∈ uIcc l (l + volume.real S),
        HasDerivAt (fun t : ℝ => (t - l) ^ 3 / 3) ((t - l) ^ 2) t := by
      intro t _
      exact ((((hasDerivAt_id t).sub_const l).pow 3).div_const 3).congr_deriv
        (by norm_num)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hc.intervalIntegrable _ _)]
    ring
  rwa [hi] at hmin

open OriginalMovingWindowMoment (width endpoint)

/-- The complete tail of the original selected set; no favorable subfamily is chosen. -/
def selectedTail (a : ℝ) (S : Set ℝ) : Set ℝ := S ∩ {t | a < endpoint t}

/-- The literal normalized endpoint moment over the complete selected tail. -/
def selectedMoment (a : ℝ) (S : Set ℝ) : ℝ :=
  ∫ t in selectedTail a S, ((endpoint t - a) / width a) ^ 2

private lemma endpoint_continuous : Continuous endpoint :=
  continuous_id.add (Real.continuous_rpow_const (by norm_num : 0 ≤ (4 / 5 : ℝ)))

private lemma endpoint_strictMono : StrictMonoOn endpoint (Ici 0) := by
  intro x hx y _ hxy
  have hw := Real.rpow_le_rpow hx hxy.le (by norm_num : 0 ≤ (4 / 5 : ℝ))
  dsimp [endpoint, width]
  linarith

private lemma endpoint_root {a : ℝ} (ha : 0 < a) :
    ∃ τ ∈ Ioo 0 a, endpoint τ = a := by
  have hzero : endpoint 0 = 0 := by norm_num [endpoint, width, Real.zero_rpow]
  have hwidth : 0 < width a := Real.rpow_pos_of_pos ha _
  have hright : a < endpoint a := by dsimp [endpoint]; linarith
  obtain ⟨τ, hτ, hroot⟩ :=
    intermediate_value_Icc ha.le endpoint_continuous.continuousOn
      (show a ∈ Icc (endpoint 0) (endpoint a) by rw [hzero]; exact ⟨ha.le, hright.le⟩)
  refine ⟨τ, ⟨?_, ?_⟩, hroot⟩
  · by_contra h
    have ht : τ = 0 := by linarith [hτ.1]
    rw [ht, hzero] at hroot
    linarith
  · by_contra h
    have ht : τ = a := by linarith [hτ.2]
    rw [ht] at hroot
    linarith

private lemma selectedTail_measurable {a : ℝ} {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (selectedTail a S) :=
  hS.inter (measurableSet_lt measurable_const endpoint_continuous.measurable)

private lemma selectedTail_subset {a τ : ℝ} {S : Set ℝ}
    (hτ : 0 ≤ τ) (hroot : endpoint τ = a) (hsub : S ⊆ Ioc 0 a) :
    selectedTail a S ⊆ Icc τ a := by
  intro t ht
  have hs := hsub ht.1
  refine ⟨?_, hs.2⟩
  by_contra h
  have hlt := endpoint_strictMono hs.1.le hτ (not_le.mp h)
  rw [hroot] at hlt
  exact (not_lt_of_ge hlt.le) ht.2

private lemma endpoint_secant {a τ t : ℝ} (hτ : 0 ≤ τ) (hτa : τ < a)
    (hroot : endpoint τ = a) (ht : t ∈ Icc τ a) :
    (t - τ) / (a - τ) ≤ (endpoint t - a) / width a := by
  have ha : 0 < a := lt_of_le_of_lt hτ hτa
  have hd : 0 < a - τ := sub_pos.mpr hτa
  have hH : 0 < width a := Real.rpow_pos_of_pos ha _
  have hc : ConcaveOn ℝ (Ici 0) endpoint :=
    (concaveOn_id (convex_Ici 0)).add
      (Real.concaveOn_rpow (by norm_num : 0 ≤ (4 / 5 : ℝ)) (by norm_num))
  have hw₁ : 0 ≤ (a - t) / (a - τ) := div_nonneg (sub_nonneg.mpr ht.2) hd.le
  have hw₂ : 0 ≤ (t - τ) / (a - τ) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hsum : (a - t) / (a - τ) + (t - τ) / (a - τ) = 1 := by
    field_simp [hd.ne']
    ring
  have hcomb : ((a - t) / (a - τ)) * τ + ((t - τ) / (a - τ)) * a = t := by
    field_simp [hd.ne']
    ring
  have hchord := hc.2 hτ ha.le hw₁ hw₂ hsum
  simp only [smul_eq_mul] at hchord
  rw [hcomb, hroot] at hchord
  have hchord' : ((a - t) * a + (t - τ) * (a + width a)) / (a - τ) ≤
      endpoint t := by
    have heq : ((a - t) * a + (t - τ) * (a + width a)) / (a - τ) =
        (a - t) / (a - τ) * a + (t - τ) / (a - τ) * endpoint a := by
      dsimp [endpoint]
      ring
    rw [heq]
    exact hchord
  have hden := (div_le_iff₀ hd).mp hchord'
  apply (div_le_div_iff₀ hd hH).mpr
  nlinarith

/-- The original tail has a sharp relaxed-set integral minimum and a cubic
secant lower bound. The crossing clock is proved to exist, rather than assumed. -/
theorem selected_endpoint_moment_bounds {a : ℝ} {S : Set ℝ}
    (ha : 0 < a) (hS : MeasurableSet S) (hsub : S ⊆ Ioc 0 a) :
    ∃ τ ∈ Ioo 0 a, endpoint τ = a ∧
      (∫ t in Icc τ (τ + volume.real (selectedTail a S)),
        ((endpoint t - a) / width a) ^ 2) ≤ selectedMoment a S ∧
      volume.real (selectedTail a S) ^ 3 / (3 * (a - τ) ^ 2) ≤
        selectedMoment a S := by
  obtain ⟨τ, hτ, hroot⟩ := endpoint_root ha
  have hs := selectedTail_measurable hS (a := a)
  have ht := selectedTail_subset hτ.1.le hroot hsub
  have hq : Continuous (fun t : ℝ => ((endpoint t - a) / width a) ^ 2) :=
    ((endpoint_continuous.sub continuous_const).div_const _).pow 2
  have hqmono : MonotoneOn (fun t : ℝ => ((endpoint t - a) / width a) ^ 2)
      (Icc τ a) := by
    intro x hx y hy hxy
    have hxB : a ≤ endpoint x := by
      rw [← hroot]
      exact endpoint_strictMono.monotoneOn hτ.1.le (hτ.1.le.trans hx.1) hx.1
    have hxyB := endpoint_strictMono.monotoneOn (hτ.1.le.trans hx.1)
      (hτ.1.le.trans hy.1) hxy
    have hH : 0 < width a := Real.rpow_pos_of_pos ha _
    have hxq : 0 ≤ (endpoint x - a) / width a := div_nonneg (sub_nonneg.mpr hxB) hH.le
    have hdiv : (endpoint x - a) / width a ≤ (endpoint y - a) / width a :=
      div_le_div_of_nonneg_right (sub_le_sub_right hxyB a) hH.le
    nlinarith
  refine ⟨τ, hτ, hroot, continuous_window_minimum hτ.2.le hs ht hq hqmono, ?_⟩
  have hd : 0 < a - τ := sub_pos.mpr hτ.2
  have hquad := quadratic_window_lower hτ.2.le hs ht
  have hnormalized : volume.real (selectedTail a S) ^ 3 / (3 * (a - τ) ^ 2) ≤
      ∫ t in selectedTail a S, ((t - τ) / (a - τ)) ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div]
    calc
      _ = (volume.real (selectedTail a S) ^ 3 / 3) / (a - τ) ^ 2 := by
        field_simp [hd.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hquad (sq_nonneg (a - τ))
  have hp : Continuous (fun t : ℝ => ((t - τ) / (a - τ)) ^ 2) :=
    ((continuous_id.sub continuous_const).div_const _).pow 2
  refine hnormalized.trans (setIntegral_mono_on
    (hp.continuousOn.integrableOn_Icc.mono_set ht)
    (hq.continuousOn.integrableOn_Icc.mono_set ht) hs ?_)
  intro t hts
  have hts' := ht hts
  have hpoint := endpoint_secant hτ.1.le hτ.2 hroot hts'
  have hpos : 0 ≤ (t - τ) / (a - τ) := div_nonneg (sub_nonneg.mpr hts'.1) hd.le
  nlinarith

end D5.S3.Arith.Robin.SelectedEndpointMoment
