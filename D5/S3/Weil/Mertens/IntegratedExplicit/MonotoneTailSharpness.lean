/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MonotoneTailSharpness
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MonotoneTailSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A monotone surrogate realizes quadratic depth and cubic weighted window mass. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A supported polynomial perturbation of the linear counting function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness

private def countOnWindow (t : ℝ) : ℝ :=
  t - t ^ 2 * (t - 2) / 16

private def count (s t : ℝ) : ℝ :=
  t + (Ioc (2 - s) (2 + s)).indicator (fun y => countOnWindow y - y) t

private def slope (t : ℝ) : ℝ := (2 - t) / 16

private def tail (A : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ t in Ioi z, (A t - t) / t ^ 2

private lemma countOnWindow_mono {u v : ℝ} (hu : 3 / 2 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 5 / 2) : countOnWindow u ≤ countOnWindow v := by
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := hu0.trans huv
  have hu' : u ≤ 5 / 2 := huv.trans hv
  have hv' : 3 / 2 ≤ v := hu.trans huv
  have hu2 : u ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hu0 hu' 2
  have hv2 : v ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hv0 hv 2
  have huv2 : u * v ≤ (5 / 2 : ℝ) * (5 / 2 : ℝ) :=
    mul_le_mul hu' hv hv0 (by norm_num)
  have hcoeff : 0 ≤ 1 - (u ^ 2 + u * v + v ^ 2 - 2 * (u + v)) / 16 := by
    linarith
  have hfactor : countOnWindow v - countOnWindow u =
      (v - u) * (1 - (u ^ 2 + u * v + v ^ 2 - 2 * (u + v)) / 16) := by
    unfold countOnWindow
    ring
  exact sub_nonneg.mp (hfactor.symm ▸ mul_nonneg (sub_nonneg.mpr huv) hcoeff)

private lemma count_eq_inside {s t : ℝ} (ht : t ∈ Ioc (2 - s) (2 + s)) :
    count s t = countOnWindow t := by simp [count, indicator_of_mem ht]

private lemma count_eq_outside {s t : ℝ} (ht : t ∉ Ioc (2 - s) (2 + s)) :
    count s t = t := by simp [count, indicator_of_notMem ht]

private lemma count_mono {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) : Monotone (count s) := by
  have lower : 2 - s ≤ countOnWindow (2 - s) := by
    unfold countOnWindow
    have h := mul_nonneg (sq_nonneg (2 - s)) hs.le
    nlinarith only [h]
  have upper : countOnWindow (2 + s) ≤ 2 + s := by
    unfold countOnWindow
    have h := mul_nonneg (sq_nonneg (2 + s)) hs.le
    nlinarith only [h]
  intro u v huv
  by_cases hu : u ∈ Ioc (2 - s) (2 + s)
  · rw [count_eq_inside hu]
    by_cases hv : v ∈ Ioc (2 - s) (2 + s)
    · rw [count_eq_inside hv]
      exact countOnWindow_mono (by linarith [hu.1]) huv (by linarith [hv.2])
    · rw [count_eq_outside hv]
      have hv' : 2 + s ≤ v := le_of_not_ge (fun h => hv ⟨hu.1.trans_le huv, h⟩)
      exact (countOnWindow_mono (by linarith [hu.1]) hu.2 (by linarith)).trans
        (upper.trans hv')
  · rw [count_eq_outside hu]
    by_cases hv : v ∈ Ioc (2 - s) (2 + s)
    · rw [count_eq_inside hv]
      have hu' : u ≤ 2 - s :=
        le_of_not_gt (fun h => hu ⟨h, huv.trans hv.2⟩)
      exact hu'.trans (lower.trans (countOnWindow_mono (by linarith) hv.1.le
        (by linarith [hv.2])))
    · rwa [count_eq_outside hv]

private lemma kernel_eq {s : ℝ} (hs : s ≤ 1 / 2) :
    (fun t => (count s t - t) / t ^ 2) = (Ioc (2 - s) (2 + s)).indicator slope := by
  funext t
  by_cases ht : t ∈ Ioc (2 - s) (2 + s)
  · rw [count_eq_inside ht, indicator_of_mem ht]
    have ht0 : 0 < t := by linarith [ht.1]
    unfold countOnWindow slope
    field_simp
    ring
  · simp [count_eq_outside ht, indicator_of_notMem ht]

private lemma slope_interval_integrable (u v : ℝ) : IntervalIntegrable slope volume u v :=
  (((continuous_const.sub continuous_id).div_const 16 : Continuous slope)).intervalIntegrable _ _

private lemma kernel_integrable {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    Integrable (fun t => (count s t - t) / t ^ 2) := by
  rw [kernel_eq hs']
  exact (integrable_indicator_iff measurableSet_Ioc).2
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : 2 - s ≤ 2 + s)).1
      (slope_interval_integrable _ _))

private lemma integral_slope (u v : ℝ) :
    ∫ t in u..v, slope t = ((u - 2) ^ 2 - (v - 2) ^ 2) / 32 := by
  calc
    _ = -((v - 2) ^ 2) / 32 - (-((u - 2) ^ 2) / 32) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => -((t - 2) ^ 2) / 32) ?_ (slope_interval_integrable u v)
      intro t _
      have hpow : HasDerivAt (fun z : ℝ => (z - 2) ^ 2) (2 * (t - 2)) t := by
        convert ((hasDerivAt_id t).sub_const (2 : ℝ)).pow 2 using 1
        · funext z
          rw [Pi.pow_apply]
          rfl
        · simp
      convert hpow.neg.div_const 32 using 1 <;> simp [slope] <;> ring
    _ = _ := by ring

private lemma tail_formula {s z : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    tail (count s) z = if 2 + s ≤ z then 0 else (((max z (2 - s)) - 2) ^ 2 - s ^ 2) / 32 := by
  unfold tail
  rw [kernel_eq hs', setIntegral_indicator measurableSet_Ioc]
  have hset : Ioi z ∩ Ioc (2 - s) (2 + s) = Ioc (max z (2 - s)) (2 + s) := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc, max_lt_iff]
    tauto
  rw [hset]
  by_cases hz : 2 + s ≤ z
  · rw [ite_eq_left hz]
    have h : 2 + s ≤ max z (2 - s) := hz.trans (le_max_left _ _)
    simp [Ioc_eq_empty (not_lt.mpr h)]
  · rw [ite_eq_right hz, ← intervalIntegral.integral_of_le
      (max_le (le_of_not_ge hz) (by linarith)), integral_slope]
    ring

private lemma window_upper {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    (∫ z in (1 : ℝ)..3, max (-tail (count s) z) 0 / Real.sqrt z) ≤ s ^ 3 / 16 := by
  let cut := Ioc (2 - s) (2 + s)
  let bound : ℝ → ℝ := cut.indicator (fun _ => s ^ 2 / 32)
  have hcount := kernel_integrable hs hs'
  have hcont : ContinuousOn (tail (count s)) (uIcc 1 3) :=
    hcount.integrableOn.continuousOn_Ici_primitive_Ioi.mono (fun z hz =>
      (uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3) ▸ hz).1)
  have hfi : IntervalIntegrable (fun z => max (-tail (count s) z) 0 / Real.sqrt z)
      volume 1 3 :=
    ((hcont.neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn (fun z hz =>
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le
        ((uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3) ▸ hz).1))).ne')).intervalIntegrable
  have hleft : (1 : ℝ) ≤ 2 - s := by linarith
  have hright : 2 + s ≤ (3 : ℝ) := by linarith
  have horder : 2 - s ≤ 2 + s := by linarith
  have hbound : IntervalIntegrable bound volume 1 3 := by
    apply Integrable.intervalIntegrable
    apply (integrable_indicator_iff measurableSet_Ioc).2
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).1 intervalIntegrable_const
  calc
    _ ≤ ∫ z in (1 : ℝ)..3, bound z := by
      apply intervalIntegral.integral_mono_on (by norm_num) hfi hbound
      intro z hz
      have hz1 : 1 ≤ Real.sqrt z := by
        simpa using Real.sqrt_le_sqrt hz.1
      rw [tail_formula hs hs']
      by_cases hu : 2 + s ≤ z
      · simp only [ite_eq_left hu, neg_zero, max_self, zero_div]
        exact indicator_nonneg (fun _ _ => by positivity) _
      · rw [ite_eq_right hu]
        by_cases hmem : z ∈ cut
        · change z ∈ Ioc (2 - s) (2 + s) at hmem
          rw [max_eq_left hmem.1.le, show bound z = s ^ 2 / 32 by
            exact indicator_of_mem hmem _]
          exact (div_le_self (le_max_right _ _) hz1).trans
            (max_le (by nlinarith [sq_nonneg (z - 2)]) (by positivity))
        · have hl : z ≤ 2 - s := le_of_not_gt (fun h => hmem ⟨h, le_of_not_ge hu⟩)
          rw [max_eq_right hl, show bound z = 0 by exact indicator_of_notMem hmem _]
          simp
    _ = s ^ 3 / 16 := by
      rw [intervalIntegral.integral_of_le (by norm_num), show bound = _ by rfl,
        setIntegral_indicator measurableSet_Ioc]
      have hsubset : cut ⊆ Ioc (1 : ℝ) 3 := Ioc_subset_Ioc hleft hright
      rw [show Ioc (1 : ℝ) 3 ∩ cut = cut from inter_eq_right.mpr hsubset]
      change (∫ z in Ioc (2 - s) (2 + s), s ^ 2 / 32) = _
      rw [← intervalIntegral.integral_of_le horder, intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- Monotonicity alone permits quadratic depths with only cubic weighted mass. -/
theorem monotone_tail_quadratic_depth_cubic_mass {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    ∃ A : ℝ → ℝ, Monotone A ∧ (∀ t ≥ 1, 0 ≤ A t) ∧
      (∀ t ∉ Icc (2 - s) (2 + s), A t = t) ∧
      Integrable (fun t => (A t - t) / t ^ 2) ∧
      let Q := fun z => ∫ t in Ioi z, (A t - t) / t ^ 2
      Q 2 = -s ^ 2 / 32 ∧ (∫ z in (1 : ℝ)..3, max (-Q z) 0 / Real.sqrt z) ≤ s ^ 3 / 16 := by
  refine ⟨count s, count_mono hs hs', ?_, ?_, kernel_integrable hs hs', ?_, window_upper hs hs'⟩
  · intro t ht
    have h1 : count s 1 = 1 := count_eq_outside (fun h => by linarith [h.1])
    have hmono := count_mono hs hs' ht
    linarith
  · intro t ht
    exact count_eq_outside (fun h => ht ⟨h.1.le, h.2⟩)
  · change tail (count s) 2 = _
    rw [tail_formula hs hs', ite_eq_right (by linarith), max_eq_left (by linarith)]
    ring

end D5.S3.Weil.Mertens.IntegratedExplicit.MonotoneTailSharpness
