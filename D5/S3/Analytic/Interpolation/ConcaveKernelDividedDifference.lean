/- GID: D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/ConcaveKernelDividedDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concave-kernel sign comparison for a second divided difference. -/

import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

import OmegaBuild.Commands

/-! A bound on the positive part of a second derivative determines the sign of its
second divided difference when the concave tent kernel preserves enough negative mass. -/

compile_only_with_mathlib

open Set MeasureTheory
open scoped Interval

namespace D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference

/-- A right-hand weighted negative contribution dominates any positive part on the left.
The same positive maximum of the kernel controls both estimates. -/
theorem integral_mul_concave_neg_of_lobe_bound
    {left right a b c : ℝ} {h k : ℝ → ℝ}
    (hinterval : left < right) (hab : a < b) (hbc : b < c) (hcr : c ≤ right)
    (hh : ContinuousOn h (Icc (min a left) right))
    (hk : ContinuousOn k (Icc left right))
    (hconcave : ConcaveOn ℝ (Icc left right) k)
    (hk_pos : ∀ t ∈ Ioo left right, 0 < k t)
    (hh_neg : ∀ t ∈ Ioo left right \ Icc a b, h t < 0)
    (hbound : (∫ t in a..b, max (h t) 0) <
      ∫ t in b..c, -h t * ((c - t) / (c - a))) :
    (∫ t in left..right, h t * k t) < 0 := by
  have hk_nonneg (t : ℝ) (ht : t ∈ Icc left right) : 0 ≤ k t := by
    have ht_closure : t ∈ closure (Ioo left right) := by
      rwa [closure_Ioo hinterval.ne]
    exact ContinuousWithinAt.closure_le ht_closure continuousWithinAt_const
      ((hk t ht).mono Ioo_subset_Icc_self) (fun u hu => (hk_pos u hu).le)
  have h_cont : ContinuousOn (fun t => h t * k t) (Icc left right) :=
    (hh.mono (Icc_subset_Icc (min_le_right ..) le_rfl)).mul hk
  have hint {u v : ℝ} (hu : left ≤ u) (huv : u ≤ v) (hv : v ≤ right) :
      IntervalIntegrable (fun t => h t * k t) volume u v :=
    (h_cont.mono (Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc (μ := volume) huv
  by_cases hleft : b ≤ left
  · have hp := intervalIntegral.intervalIntegral_pos_of_pos_on
        (hint le_rfl hinterval.le le_rfl).neg
        (fun t ht => neg_pos.mpr (mul_neg_of_neg_of_pos
          (hh_neg t ⟨ht, fun ht' => (ht' : t ∈ Icc a b).2.not_gt (hleft.trans_lt ht.1)⟩)
          (hk_pos t ht))) hinterval
    change 0 < ∫ t in left..right, -(h t * k t) at hp
    rwa [intervalIntegral.integral_neg, neg_pos] at hp
  have hlb : left < b := lt_of_not_ge hleft
  have hbr : b < right := hbc.trans_le hcr
  let d := max a left
  have had : a ≤ d := le_max_left ..
  have hld : left ≤ d := le_max_right ..
  have hdb : d < b := max_lt hab hlb
  obtain ⟨p, hp, hp_max⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hdb.le) (hk.mono (Icc_subset_Icc hld hbr.le))
  have hm : 0 < k p :=
    (hk_pos b ⟨hlb, hbr⟩).trans_le (hp_max (right_mem_Icc.mpr hdb.le))
  have hpr : p ∈ Icc left right := ⟨hld.trans hp.1, hp.2.trans hbr.le⟩
  have hcl : c ∈ Icc left right := ⟨(hlb.trans hbc).le, hcr⟩
  have hpc : p < c := hp.2.trans_lt hbc
  have hleft_integral : (∫ t in left..d, h t * k t) ≤ 0 := by
    simpa using intervalIntegral.integral_mono_on_of_le_Ioo hld
      (hint le_rfl hld (hdb.trans hbr).le) (intervalIntegrable_const (c := (0 : ℝ)))
      (fun t ht => by
        have hta : t < a := (lt_max_iff.mp ht.2).resolve_right ht.1.not_gt
        have ht' : t ∈ Ioo left right := ⟨ht.1, ht.2.trans (hdb.trans hbr)⟩
        exact mul_nonpos_of_nonpos_of_nonneg
          (hh_neg t ⟨ht', fun h => hta.not_ge (h : t ∈ Icc a b).1⟩).le
          (hk_nonneg t (Ioo_subset_Icc_self ht')))
  have hright_integral : (∫ t in c..right, h t * k t) ≤ 0 := by
    simpa using intervalIntegral.integral_mono_on_of_le_Ioo hcr
      (hint hcl.1 hcr le_rfl) (intervalIntegrable_const (c := (0 : ℝ)))
      (fun t ht => by
        have ht' : t ∈ Ioo left right := ⟨hcl.1.trans_lt ht.1, ht.2⟩
        exact mul_nonpos_of_nonpos_of_nonneg
          (hh_neg t ⟨ht', fun h => (hbc.trans ht.1).not_ge (h : t ∈ Icc a b).2⟩).le
          (hk_nonneg t (Ioo_subset_Icc_self ht')))
  have hpos_cont : ContinuousOn (fun t => max (h t) 0) (Icc a b) :=
    (hh.mono (Icc_subset_Icc (min_le_left ..) hbr.le)).sup continuousOn_const
  have hpos_hint := hpos_cont.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hmid_integral : (∫ t in d..b, h t * k t) ≤
      k p * ∫ t in a..b, max (h t) 0 := by
    have hd_hint :=
      (hpos_cont.mono (Icc_subset_Icc had le_rfl)).intervalIntegrable_of_Icc (μ := volume) hdb.le
    calc
      (∫ t in d..b, h t * k t) ≤ ∫ t in d..b, k p * max (h t) 0 := by
        apply intervalIntegral.integral_mono_on hdb.le
          (hint hld hdb.le hbr.le) (hd_hint.const_mul _)
        intro t ht
        have ht' : t ∈ Icc left right := ⟨hld.trans ht.1, ht.2.trans hbr.le⟩
        exact (mul_le_mul_of_nonneg_right (le_max_left ..) (hk_nonneg t ht')).trans
          ((mul_le_mul_of_nonneg_left (hp_max ht) (le_max_right ..)).trans_eq (mul_comm ..))
      _ = k p * ∫ t in d..b, max (h t) 0 := intervalIntegral.integral_const_mul _ _
      _ ≤ k p * ∫ t in a..b, max (h t) 0 := by
        apply mul_le_mul_of_nonneg_left _ hm.le
        exact intervalIntegral.integral_mono_interval had hdb.le le_rfl
          (Filter.Eventually.of_forall fun t => le_max_right ..) hpos_hint
  have hweight (t : ℝ) (ht : t ∈ Ioo b c) :
      k p * ((c - t) / (c - a)) ≤ k t := by
    have hpt : p ≤ t := hp.2.trans ht.1.le
    have hct : 0 ≤ c - t := sub_nonneg.mpr ht.2.le
    have hfrac : (c - t) / (c - a) ≤ (c - t) / (c - p) :=
      div_le_div_of_nonneg_left hct (sub_pos.mpr hpc) (sub_le_sub_left (had.trans hp.1) _)
    have hfirst : 0 ≤ (c - t) / (c - p) := div_nonneg hct (sub_nonneg.mpr hpc.le)
    have hsecond : 0 ≤ (t - p) / (c - p) :=
      div_nonneg (sub_nonneg.mpr hpt) (sub_nonneg.mpr hpc.le)
    have hsum : (c - t) / (c - p) + (t - p) / (c - p) = 1 := by
      rw [← add_div]
      rw [show c - t + (t - p) = c - p by ring, div_self (sub_ne_zero.mpr hpc.ne')]
    have hpoint : (c - t) / (c - p) * p + (t - p) / (c - p) * c = t := by
      field_simp [sub_ne_zero.mpr hpc.ne']
      ring
    have hchord := hconcave.2 hpr hcl hfirst hsecond hsum
    simp only [smul_eq_mul, hpoint] at hchord
    calc
      k p * ((c - t) / (c - a)) ≤ k p * ((c - t) / (c - p)) :=
        mul_le_mul_of_nonneg_left hfrac hm.le
      _ ≤ (c - t) / (c - p) * k p + (t - p) / (c - p) * k c := by
        rw [mul_comm (k p)]
        exact le_add_of_nonneg_right (mul_nonneg hsecond (hk_nonneg c hcl))
      _ ≤ k t := hchord
  have hweighted_cont : ContinuousOn (fun t => -h t * ((c - t) / (c - a))) (Icc b c) :=
    (hh.mono (Icc_subset_Icc ((min_le_left ..).trans hab.le) hcr)).neg.mul
      ((continuous_const.sub continuous_id).div_const _).continuousOn
  have hweight_integral : (∫ t in b..c, h t * k t) ≤
      -(k p * ∫ t in b..c, -h t * ((c - t) / (c - a))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hbc.le
      (hint hlb.le hbc.le hcr)
      ((hweighted_cont.intervalIntegrable_of_Icc (μ := volume) hbc.le).const_mul _).neg
    intro t ht
    have ht' : t ∈ Ioo left right := ⟨hlb.trans ht.1, ht.2.trans_le hcr⟩
    have hnt := hh_neg t ⟨ht', fun h => ht.1.not_ge (h : t ∈ Icc a b).2⟩
    calc
      h t * k t ≤ h t * (k p * ((c - t) / (c - a))) :=
        mul_le_mul_of_nonpos_left (hweight t ht) hnt.le
      _ = -(k p * (-h t * ((c - t) / (c - a)))) := by ring
  have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
    (hint le_rfl hld (hdb.trans hbr).le) (hint hld hdb.le hbr.le)
  have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
    (hint le_rfl hlb.le hbr.le) (hint hlb.le hbc.le hcr)
  have hadd₃ := intervalIntegral.integral_add_adjacent_intervals
    (hint le_rfl hcl.1 hcr) (hint hcl.1 hcr le_rfl)
  linarith [mul_lt_mul_of_pos_left hbound hm]


private theorem intervalIntegral_tent_eq_slope_sub_slope
    {left mid right : ℝ} {f fp fpp : ℝ → ℝ}
    (hlm : left < mid) (hmr : mid < right)
    (hf : ∀ t ∈ Icc left right, HasDerivAt f (fp t) t)
    (hfp : ∀ t ∈ Icc left right, HasDerivAt fp (fpp t) t)
    (hfpp : ContinuousOn fpp (Icc left right)) :
    (∫ t in left..right, fpp t *
      min ((t - left) / (mid - left)) ((right - t) / (right - mid))) =
      (f right - f mid) / (right - mid) - (f mid - f left) / (mid - left) := by
  let up (t : ℝ) := (t - left) / (mid - left)
  let down (t : ℝ) := (right - t) / (right - mid)
  have hup (t : ℝ) : HasDerivAt up (1 / (mid - left)) t :=
    ((hasDerivAt_id' t).sub_const left).div_const (mid - left)
  have hdown (t : ℝ) : HasDerivAt down (-1 / (right - mid)) t :=
    ((hasDerivAt_id' t).const_sub right).div_const (right - mid)
  have hcut : ContinuousOn (fun t => fpp t * min (up t) (down t)) (Icc left right) :=
    hfpp.mul ((continuous_iff_continuousAt.mpr fun t => (hup t).continuousAt).inf
      (continuous_iff_continuousAt.mpr fun t => (hdown t).continuousAt)).continuousOn
  have hint₁ := (hcut.mono (Icc_subset_Icc le_rfl hmr.le)).intervalIntegrable_of_Icc
    (μ := volume) hlm.le
  have hint₂ := (hcut.mono (Icc_subset_Icc hlm.le le_rfl)).intervalIntegrable_of_Icc
    (μ := volume) hmr.le
  have hfp_cont : ContinuousOn fp (Icc left right) :=
    fun t ht => (hfp t ht).continuousAt.continuousWithinAt
  have h₁ (t : ℝ) (ht : t ∈ Icc left mid) : up t ≤ down t := by
    have hl : up t ≤ 1 := (div_le_iff₀ (sub_pos.mpr hlm)).mpr (by linarith [ht.2])
    have hr : 1 ≤ down t := (le_div_iff₀ (sub_pos.mpr hmr)).mpr (by linarith [ht.2])
    exact hl.trans hr
  have h₂ (t : ℝ) (ht : t ∈ Icc mid right) : down t ≤ up t := by
    have hl : 1 ≤ up t := (le_div_iff₀ (sub_pos.mpr hlm)).mpr (by linarith [ht.1])
    have hr : down t ≤ 1 := (div_le_iff₀ (sub_pos.mpr hmr)).mpr (by linarith [ht.1])
    exact hr.trans hl
  have hleft : (∫ t in left..mid, fpp t * min (up t) (down t)) =
      ∫ t in left..mid, up t * fpp t := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le hlm.le] at ht
    simp only [min_eq_left (h₁ t ht), mul_comm]
  have hright : (∫ t in mid..right, fpp t * min (up t) (down t)) =
      ∫ t in mid..right, down t * fpp t := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le hmr.le] at ht
    simp only [min_eq_right (h₂ t ht), mul_comm]
  have hleft_fpp := (hfpp.mono (Icc_subset_Icc le_rfl hmr.le)).intervalIntegrable_of_Icc
    (μ := volume) hlm.le
  have hright_fpp := (hfpp.mono (Icc_subset_Icc hlm.le le_rfl)).intervalIntegrable_of_Icc
    (μ := volume) hmr.le
  have hleft_fp := (hfp_cont.mono (Icc_subset_Icc le_rfl hmr.le)).intervalIntegrable_of_Icc
    (μ := volume) hlm.le
  have hright_fp := (hfp_cont.mono (Icc_subset_Icc hlm.le le_rfl)).intervalIntegrable_of_Icc
    (μ := volume) hmr.le
  have hlparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t (_ : t ∈ uIcc left mid) => hup t)
    (fun t ht => hfp t (Icc_subset_Icc le_rfl hmr.le (by rwa [uIcc_of_le hlm.le] at ht)))
    intervalIntegrable_const hleft_fpp
  have hrparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t (_ : t ∈ uIcc mid right) => hdown t)
    (fun t ht => hfp t (Icc_subset_Icc hlm.le le_rfl (by rwa [uIcc_of_le hmr.le] at ht)))
    intervalIntegrable_const hright_fpp
  have hlftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hf t (Icc_subset_Icc le_rfl hmr.le (by rwa [uIcc_of_le hlm.le] at ht))) hleft_fp
  have hrftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hf t (Icc_subset_Icc hlm.le le_rfl (by rwa [uIcc_of_le hmr.le] at ht))) hright_fp
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂, hleft, hright, hlparts,
    hrparts, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hlftc, hrftc]
  simp [up, down, sub_ne_zero.mpr hlm.ne', sub_ne_zero.mpr hmr.ne', div_eq_mul_inv]
  ring

/-- The adjacent secant slopes strictly decrease under a weighted bound on the
positive part of the second derivative. -/
theorem three_node_slope_sub_slope_neg_of_lobe_bound
    {left mid right a b c : ℝ} {f fp fpp : ℝ → ℝ}
    (hlm : left < mid) (hmr : mid < right) (hab : a < b) (hbc : b < c) (hcr : c ≤ right)
    (hf : ∀ t ∈ Icc left right, HasDerivAt f (fp t) t)
    (hfp : ∀ t ∈ Icc left right, HasDerivAt fp (fpp t) t)
    (hfpp : ContinuousOn fpp (Icc (min a left) right))
    (hneg : ∀ t ∈ Ioo left right \ Icc a b, fpp t < 0)
    (hbound : (∫ t in a..b, max (fpp t) 0) <
      ∫ t in b..c, -fpp t * ((c - t) / (c - a))) :
    (f right - f mid) / (right - mid) < (f mid - f left) / (mid - left) := by
  let up (t : ℝ) := (t - left) / (mid - left)
  let down (t : ℝ) := (right - t) / (right - mid)
  have hu : Continuous up := (continuous_id.sub continuous_const).div_const _
  have hd : Continuous down := (continuous_const.sub continuous_id).div_const _
  have hconvex : Convex ℝ (Icc left right) := convex_Icc ..
  have huc : ConcaveOn ℝ (Icc left right) up := by
    refine ⟨hconvex, fun x hx y hy r s hr hs hrs => ?_⟩
    simp only [smul_eq_mul, up]
    apply le_of_eq
    have hsum : r + s = 1 := hrs
    linear_combination -left / (mid - left) * hsum
  have hdc : ConcaveOn ℝ (Icc left right) down := by
    refine ⟨hconvex, fun x hx y hy r s hr hs hrs => ?_⟩
    simp only [smul_eq_mul, down]
    apply le_of_eq
    have hsum : r + s = 1 := hrs
    linear_combination right / (right - mid) * hsum
  have hpos (t : ℝ) (ht : t ∈ Ioo left right) : 0 < min (up t) (down t) :=
    lt_min (div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hlm))
      (div_pos (sub_pos.mpr ht.2) (sub_pos.mpr hmr))
  have hsign := integral_mul_concave_neg_of_lobe_bound (hlm.trans hmr) hab hbc hcr hfpp
    (hu.inf hd).continuousOn (huc.inf hdc) hpos hneg hbound
  have hid := intervalIntegral_tent_eq_slope_sub_slope hlm hmr hf hfp
    (hfpp.mono (Icc_subset_Icc (min_le_right ..) le_rfl))
  exact sub_neg.mp (hid ▸ hsign)

end D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference
