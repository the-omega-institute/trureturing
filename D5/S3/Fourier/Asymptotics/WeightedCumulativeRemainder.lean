/- GID: D5/S3/Fourier/Asymptotics/WeightedCumulativeRemainder
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/WeightedCumulativeRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An envelope controls the weighted remainder of a cumulative error. -/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! A differentiable envelope for a cumulative error can be carried through a
decreasing weight without bounding the envelope by its value at the right endpoint. -/

open MeasureTheory Set
open scoped Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder

open Finset intervalIntegral

/-- For a finite multiset of jumps in the height interval, the weighted sum
is the terminal cumulative sum minus the integral against the weight derivative. -/
private theorem finite_abel_identity {ι : Type*} (s : Finset ι) (height : ι → ℝ)
    (amplitude : ι → ℂ) {X T : ℝ} (hXT : X ≤ T)
    (hheight : ∀ i ∈ s, height i ∈ Ioc X T) (w w' : ℝ → ℝ)
    (hw : ∀ t ∈ [[X, T]], HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' [[X, T]]) :
    ∑ i ∈ s, (w (height i) : ℂ) * amplitude i =
      (w T : ℂ) * (∑ i ∈ s, amplitude i) -
        ∫ t in X..T, (w' t : ℂ) * (∑ i ∈ s, if height i ≤ t then amplitude i else 0) := by
  classical
  let f (i : ι) := (Ici (height i)).indicator (fun t => (w' t : ℂ) * amplitude i)
  have hcont (i : ι) : ContinuousOn (fun t => (w' t : ℂ) * amplitude i) [[X, T]] :=
    (Complex.continuous_ofReal.comp_continuousOn hw').mul continuousOn_const
  have hi (i : ι) (_ : i ∈ s) : IntervalIntegrable (f i) volume X T :=
    intervalIntegrable_iff.mpr ((hcont i).intervalIntegrable.def'.indicator measurableSet_Ici)
  have hlocal (i : ι) (hm : i ∈ s) :
      (∫ t in X..T, f i t) = ((w T : ℂ) - w (height i)) * amplitude i := by
    obtain ⟨hXi, hiT⟩ := hheight i hm
    have hleft := (hi i hm).mono_set (by
      rw [uIcc_of_le hXi.le, uIcc_of_le hXT]
      exact Icc_subset_Icc_right hiT)
    have hright := (hi i hm).mono_set (by
      rw [uIcc_of_le hiT, uIcc_of_le hXT]
      exact Icc_subset_Icc_left hXi.le)
    have hzero : (∫ t in X..height i, f i t) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le hXi.le] at ht
      exact indicator_of_notMem (not_le.mpr ht.2) _
    have hunmask : (∫ t in height i..T, f i t) =
        ∫ t in height i..T, (w' t : ℂ) * amplitude i := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le hiT] at ht
      exact indicator_of_mem ht.1.le _
    have hsub : [[height i, T]] ⊆ [[X, T]] := by
      rw [uIcc_of_le hiT, uIcc_of_le hXT]
      exact Icc_subset_Icc_left hXi.le
    have hftc :
        (∫ t in height i..T, (w' t : ℂ) * amplitude i) =
          (w T : ℂ) * amplitude i - (w (height i) : ℂ) * amplitude i :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => ((hw t (hsub ht)).ofReal_comp).mul_const (amplitude i))
        (((hcont i).mono hsub).intervalIntegrable)
    rw [← integral_add_adjacent_intervals hleft hright, hzero, zero_add, hunmask, hftc, sub_mul]
  have hsum :
      (∫ t in X..T, (w' t : ℂ) * (∑ i ∈ s, if height i ≤ t then amplitude i else 0)) =
        ∑ i ∈ s, ((w T : ℂ) - w (height i)) * amplitude i := by
    calc
      _ = ∫ t in X..T, ∑ i ∈ s, f i t := by
        apply intervalIntegral.integral_congr
        intro t _
        change (w' t : ℂ) * (∑ i ∈ s, if height i ≤ t then amplitude i else 0) =
          ∑ i ∈ s, f i t
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        by_cases h : height i ≤ t <;> simp [f, h]
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum hi]
        exact sum_congr rfl hlocal
  rw [hsum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

/-- The two endpoint errors and the error integrated against the weight derivative
are controlled by the envelope at the left endpoint and its accumulated growth. -/
private theorem norm_weighted_remainder_le
    {X T : ℝ} (hXT : X ≤ T) (w w' E E' : ℝ → ℝ) (R : ℝ → ℂ)
    (hw : ∀ t ∈ [[X, T]], HasDerivAt w (w' t) t)
    (hE : ∀ t ∈ [[X, T]], HasDerivAt E (E' t) t)
    (hw' : ContinuousOn w' [[X, T]]) (hE' : ContinuousOn E' [[X, T]])
    (hwpos : ∀ t ∈ [[X, T]], 0 ≤ w t) (hwslope : ∀ t ∈ [[X, T]], w' t ≤ 0)
    (hR : IntervalIntegrable R volume X T) (hbound : ∀ t ∈ [[X, T]], ‖R t‖ ≤ E t) :
    ‖(w T : ℂ) * R T - (w X : ℂ) * R X -
      ∫ t in X..T, (w' t : ℂ) * R t‖ ≤
      2 * w X * E X + ∫ t in X..T, w t * E' t := by
  have hwc : ContinuousOn w [[X, T]] := HasDerivAt.continuousOn hw
  have hEc : ContinuousOn E [[X, T]] := HasDerivAt.continuousOn hE
  have hi : IntervalIntegrable (fun t => (w' t : ℂ) * R t) volume X T :=
    hR.continuousOn_mul (Complex.continuous_ofReal.comp_continuousOn hw')
  have hq : IntervalIntegrable (fun t => -w' t * E t) volume X T :=
    (hw'.neg.mul hEc).intervalIntegrable
  have hpart := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hwc hEc (fun t ht => hw t (Ioo_subset_Icc_self ht))
    (fun t ht => hE t (Ioo_subset_Icc_self ht)) hw'.intervalIntegrable hE'.intervalIntegrable
  have herror : ‖∫ t in X..T, (w' t : ℂ) * R t‖ ≤ ∫ t in X..T, -w' t * E t := by
    refine (intervalIntegral.norm_integral_le_integral_norm hXT).trans
      (intervalIntegral.integral_mono_on hXT hi.norm hq ?_)
    intro t ht
    have ht' : t ∈ [[X, T]] := by rwa [uIcc_of_le hXT]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hwslope t ht')]
    exact mul_le_mul_of_nonneg_left (hbound t ht') (neg_nonneg.mpr (hwslope t ht'))
  have hendpoint (t : ℝ) (ht : t ∈ [[X, T]]) : ‖(w t : ℂ) * R t‖ ≤ w t * E t := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hwpos t ht)]
    exact mul_le_mul_of_nonneg_left (hbound t ht) (hwpos t ht)
  calc
    _ ≤ ‖(w T : ℂ) * R T‖ + ‖(w X : ℂ) * R X‖ +
        ‖∫ t in X..T, (w' t : ℂ) * R t‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ w T * E T + w X * E X + ∫ t in X..T, -w' t * E t :=
      add_le_add (add_le_add (hendpoint T right_mem_uIcc) (hendpoint X left_mem_uIcc)) herror
    _ = _ := by
      simp_rw [neg_mul, intervalIntegral.integral_neg]
      linarith

private theorem log_scale_hasDerivAt {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Real.log (c * u)) (1 / t) t := by
  convert ((hasDerivAt_id t).const_mul c).log (mul_pos hc ht).ne' using 1
  · rfl
  · simp only [mul_one, id_eq]
    field_simp [hc.ne', ht.ne']

private theorem log_remainder_primitive {c A B t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => -((2 * A * (Real.log (c * u) + 1) + B) / u))
      ((2 * A * Real.log (c * t) + B) / t ^ 2) t := by
  convert (((((log_scale_hasDerivAt hc ht).add_const 1).const_mul (2 * A)).add_const B).div
    (hasDerivAt_id t) ht.ne').neg using 1
  · rfl
  · simp only [id_eq]
    field_simp [ht.ne']
    ring

/-- A logarithmic cumulative error gives a remainder bound uniform in the upper height. -/
private theorem norm_weighted_log_remainder_le
    {X T c A B : ℝ} (hX : 1 ≤ X) (hXT : X ≤ T) (hc : 1 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w w' : ℝ → ℝ) (R : ℝ → ℂ)
    (hw : ∀ t ∈ [[X, T]], HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' [[X, T]])
    (hwpos : ∀ t ∈ [[X, T]], 0 ≤ w t) (hwslope : ∀ t ∈ [[X, T]], w' t ≤ 0)
    (hwcap : ∀ t ∈ [[X, T]], w t ≤ 1 / t) (hR : IntervalIntegrable R volume X T)
    (hbound : ∀ t ∈ [[X, T]], ‖R t‖ ≤ A * Real.log (c * t) ^ 2 + B * Real.log (2 * t)) :
    ‖(w T : ℂ) * R T - (w X : ℂ) * R X -
      ∫ t in X..T, (w' t : ℂ) * R t‖ ≤
      (2 * A * (Real.log (c * X) ^ 2 + Real.log (c * X) + 1) +
        B * (2 * Real.log (2 * X) + 1)) / X := by
  let E (t : ℝ) := A * Real.log (c * t) ^ 2 + B * Real.log (2 * t)
  let E' (t : ℝ) := (2 * A * Real.log (c * t) + B) / t
  let F (t : ℝ) := -((2 * A * (Real.log (c * t) + 1) + B) / t)
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have ht1 (t : ℝ) (ht : t ∈ [[X, T]]) : 1 ≤ t := by
    rw [uIcc_of_le hXT] at ht
    exact hX.trans ht.1
  have htpos (t : ℝ) (ht : t ∈ [[X, T]]) : 0 < t := zero_lt_one.trans_le (ht1 t ht)
  have hlog (t : ℝ) (ht : t ∈ [[X, T]]) : 0 ≤ Real.log (c * t) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hc (ht1 t ht))
  have hnum (t : ℝ) (ht : t ∈ [[X, T]]) : 0 ≤ 2 * A * Real.log (c * t) + B :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) (hlog t ht)) hB
  have hlogc : ContinuousOn (fun t : ℝ => Real.log (c * t)) [[X, T]] :=
    HasDerivAt.continuousOn fun t ht => log_scale_hasDerivAt hc0 (htpos t ht)
  have hE (t : ℝ) (ht : t ∈ [[X, T]]) : HasDerivAt E (E' t) t := by
    have h := (((log_scale_hasDerivAt hc0 (htpos t ht)).pow 2).const_mul A).add
      ((log_scale_hasDerivAt (by norm_num : (0 : ℝ) < 2) (htpos t ht)).const_mul B)
    convert h using 1
    simp only [E', Nat.cast_ofNat]
    ring
  have hcontN : ContinuousOn (fun t : ℝ => 2 * A * Real.log (c * t) + B) [[X, T]] :=
    (continuousOn_const.mul hlogc).add continuousOn_const
  have hE' : ContinuousOn E' [[X, T]] :=
    hcontN.div continuousOn_id (fun t ht => (htpos t ht).ne')
  have hcontB : ContinuousOn (fun t : ℝ => (2 * A * Real.log (c * t) + B) / t ^ 2) [[X, T]] :=
    hcontN.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (htpos t ht).ne')
  have hboundE : 0 ≤ E X := (norm_nonneg _).trans (hbound X left_mem_uIcc)
  have hI :
      (∫ t in X..T, w t * E' t) ≤
        ∫ t in X..T, (2 * A * Real.log (c * t) + B) / t ^ 2 := by
    refine integral_mono_on hXT ((HasDerivAt.continuousOn hw).mul hE').intervalIntegrable
      hcontB.intervalIntegrable ?_
    intro t ht
    have ht' : t ∈ [[X, T]] := by rwa [uIcc_of_le hXT]
    calc
      _ ≤ (1 / t) * E' t :=
        mul_le_mul_of_nonneg_right (hwcap t ht') (div_nonneg (hnum t ht') (htpos t ht').le)
      _ = _ := by simp only [E']; ring
  have hFTC :
      (∫ t in X..T, (2 * A * Real.log (c * t) + B) / t ^ 2) = F T - F X :=
    integral_eq_sub_of_hasDerivAt
      (fun t ht => log_remainder_primitive hc0 (htpos t ht)) hcontB.intervalIntegrable
  have hFT : F T ≤ 0 := by
    apply neg_nonpos.mpr
    exact div_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA)
        (by linarith [hlog T right_mem_uIcc])) hB)
      (htpos T right_mem_uIcc).le
  calc
    _ ≤ 2 * w X * E X + ∫ t in X..T, w t * E' t :=
      norm_weighted_remainder_le hXT w w' E E' R hw hE hw' hE' hwpos hwslope hR hbound
    _ ≤ 2 * (1 / X) * E X + (F T - F X) := by
      rw [← hFTC]
      exact add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hwcap X left_mem_uIcc) (by norm_num)) hboundE) hI
    _ ≤ 2 * (1 / X) * E X - F X := by linarith
    _ = _ := by simp only [E, F]; ring

/-- Transfer a cumulative logarithmic error to a weighted finite sum minus a smooth
main term, with heights at the right endpoint included. -/
theorem weighted_tail_error_le
    {ι : Type*} (s : Finset ι) (height : ι → ℝ) (amplitude : ι → ℂ)
    {X T c A B : ℝ} (hX : 1 ≤ X) (hXT : X ≤ T) (hc : 1 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hheight : ∀ i ∈ s, height i ∈ Ioc X T) (w w' : ℝ → ℝ)
    (hw : ∀ t ∈ [[X, T]], HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' [[X, T]])
    (hwpos : ∀ t ∈ [[X, T]], 0 ≤ w t) (hwslope : ∀ t ∈ [[X, T]], w' t ≤ 0)
    (hwcap : ∀ t ∈ [[X, T]], w t ≤ 1 / t)
    (baseline : ℂ) (G g : ℝ → ℂ)
    (hG : ∀ t ∈ [[X, T]], HasDerivAt G (g t) t) (hg : ContinuousOn g [[X, T]])
    (herror : ∀ t ∈ [[X, T]],
      ‖baseline + (∑ i ∈ s, if height i ≤ t then amplitude i else 0) - G t‖ ≤
        A * Real.log (c * t) ^ 2 + B * Real.log (2 * t)) :
    let size : ℂ → ℝ := fun z => ‖z‖
    size ((∑ i ∈ s, (w (height i) : ℂ) * amplitude i) -
      ∫ t in X..T, (w t : ℂ) * g t) ≤
      (2 * A * (Real.log (c * X) ^ 2 + Real.log (c * X) + 1) +
        B * (2 * Real.log (2 * X) + 1)) / X := by
  classical
  let C (t : ℝ) := ∑ i ∈ s, if height i ≤ t then amplitude i else 0
  let main (t : ℝ) := G t - baseline
  let R (t : ℝ) := C t - main t
  have hmain (t : ℝ) (ht : t ∈ [[X, T]]) : HasDerivAt main (g t) t :=
    (hG t ht).sub_const baseline
  have hmainc : ContinuousOn main [[X, T]] := HasDerivAt.continuousOn hmain
  have hC : IntervalIntegrable C volume X T := by
    have ht (i : ι) (_ : i ∈ s) :
        IntervalIntegrable (fun t : ℝ => if height i ≤ t then amplitude i else 0) volume X T := by
      have hi : IntervalIntegrable (fun _ : ℝ => amplitude i) volume X T :=
        continuous_const.intervalIntegrable _ _
      have he : (fun t : ℝ => if height i ≤ t then amplitude i else 0) =
          (Ici (height i)).indicator (fun _ => amplitude i) := by
        funext t
        by_cases ht : height i ≤ t <;> simp [Set.indicator, ht]
      rw [he]
      exact intervalIntegrable_iff.mpr (hi.def'.indicator measurableSet_Ici)
    have he : C = ∑ i ∈ s, (fun t : ℝ => if height i ≤ t then amplitude i else 0) := by
      funext t
      rw [Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum s ht
  have hR : IntervalIntegrable R volume X T := hC.sub hmainc.intervalIntegrable
  have hbound (t : ℝ) (ht : t ∈ [[X, T]]) :
      ‖R t‖ ≤ A * Real.log (c * t) ^ 2 + B * Real.log (2 * t) := by
    have he : R t = baseline + C t - G t := by
      dsimp [R, main]
      ring
    rw [he]
    exact herror t ht
  have hsmall := norm_weighted_log_remainder_le hX hXT hc hA hB w w' R
    hw hw' hwpos hwslope hwcap hR hbound
  have hCX : C X = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (not_le_of_gt (hheight i hi).1)
  have hCT : C T = ∑ i ∈ s, amplitude i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_left (hheight i hi).2
  have hab := finite_abel_identity s height amplitude hXT hheight w w' hw hw'
  change (∑ i ∈ s, (w (height i) : ℂ) * amplitude i) =
    (w T : ℂ) * (∑ i ∈ s, amplitude i) - ∫ t in X..T, (w' t : ℂ) * C t at hab
  rw [← hCT] at hab
  have hd : ContinuousOn (fun t => (w' t : ℂ)) [[X, T]] :=
    Complex.continuous_ofReal.comp_continuousOn hw'
  have hp := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t => (w t : ℂ)) (u' := fun t => (w' t : ℂ))
    (v := main) (v' := g)
    (Complex.continuous_ofReal.comp_continuousOn (HasDerivAt.continuousOn hw)) hmainc
    (fun t ht => (hw t (Ioo_subset_Icc_self ht)).ofReal_comp)
    (fun t ht => hmain t (Ioo_subset_Icc_self ht)) hd.intervalIntegrable hg.intervalIntegrable
  have hi :
      (∫ t in X..T, (w' t : ℂ) * R t) =
        (∫ t in X..T, (w' t : ℂ) * C t) - ∫ t in X..T, (w' t : ℂ) * main t := by
    have hm : IntervalIntegrable (fun t => (w' t : ℂ) * main t) volume X T :=
      (hd.mul hmainc).intervalIntegrable
    rw [← intervalIntegral.integral_sub (hC.continuousOn_mul hd) hm]
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_sub _ _ _
  dsimp only
  rw [hab, hp]
  convert hsmall using 2
  rw [hi]
  simp only [R, hCX]
  ring

end D5.S3.Fourier.Asymptotics.WeightedCumulativeRemainder
