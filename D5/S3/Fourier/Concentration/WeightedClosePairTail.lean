/- GID: D5/S3/Fourier/Concentration/WeightedClosePairTail
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/WeightedClosePairTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cumulative close-pair mass bounds reciprocal-product weights by partial summation. -/

import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Smoothing

/-! Partial summation over the maximum ordinate of each close pair. -/

set_option autoImplicit false

namespace D5.S3.Fourier.Concentration.WeightedClosePairTail

open Finset Set MeasureTheory intervalIntegral

/-- The height-dependent factor in the uniform weighted pair bound. -/
noncomputable def reciprocalLogTail (x : ℝ) : ℝ := (Real.log x + 1) / x

private theorem inverse_cube_continuous {x T : ℝ} (hx : 0 < x) :
    ContinuousOn (fun t : ℝ => 2 / t ^ 3) (Icc x T) :=
  continuousOn_const.div (continuousOn_id.pow 3) fun _ ht =>
    pow_ne_zero 3 (hx.trans_le ht.1).ne'

private theorem inverse_cube_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 2 / t ^ 3) = 1 / a ^ 2 - 1 / b ^ 2 := by
  have hn : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    exact fun h => ha.not_ge h.1
  have h := integral_zpow (a := a) (b := b) (n := -3) (Or.inr ⟨by norm_num, hn⟩)
  rw [show (fun t : ℝ => 2 / t ^ 3) = fun t => 2 * t ^ (-3 : ℤ) by
    funext t
    simp [zpow_neg, div_eq_mul_inv]]
  rw [intervalIntegral.integral_const_mul, h]
  norm_num [zpow_neg, div_eq_mul_inv]
  ring

private theorem log_decay_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t / t ^ 2) =
      (Real.log a + 1) / a - (Real.log b + 1) / b := by
  convert ConjectureMachines.Semantics.Riemann.WeightedStieltjes.intervalIntegral_riemannVonMangoldt_div_cube
    ha hab 1 0 0 using 1
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    field_simp [ht0] <;> ring
  · ring

private theorem restricted_integral {x y T : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyT : y ≤ T)
    (c : ℝ) :
    (∫ t in x..T, (Ici y).indicator (fun t : ℝ => c * (2 / t ^ 3)) t) =
      c * (1 / y ^ 2 - 1 / T ^ 2) := by
  have hF : IntervalIntegrable (fun t : ℝ => c * (2 / t ^ 3)) volume x T :=
    (continuousOn_const.mul (inverse_cube_continuous hx)).intervalIntegrable_of_Icc
      (hxy.trans hyT)
  have hInd : IntervalIntegrable ((Ici y).indicator (fun t : ℝ => c * (2 / t ^ 3))) volume x T :=
    intervalIntegrable_iff.mpr (hF.def'.indicator measurableSet_Ici)
  have hA := hInd.mono_set (by
    rw [uIcc_of_le hxy, uIcc_of_le (hxy.trans hyT)]
    exact Set.Icc_subset_Icc_right hyT)
  have hB := hInd.mono_set (by
    rw [uIcc_of_le hyT, uIcc_of_le (hxy.trans hyT)]
    exact Set.Icc_subset_Icc_left hxy)
  rw [← integral_add_adjacent_intervals hA hB]
  have hleft : (∫ t in x..y, (Ici y).indicator (fun t : ℝ => c * (2 / t ^ 3)) t) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hxy] at ht
    exact indicator_of_notMem (not_le_of_gt ht.2) _
  have hright :
      (∫ t in y..T, (Ici y).indicator (fun t : ℝ => c * (2 / t ^ 3)) t) =
        ∫ t in y..T, c * (2 / t ^ 3) := by
    apply integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hyT] at ht
    exact indicator_of_mem ht.1.le _
  rw [hleft, zero_add, hright, intervalIntegral.integral_const_mul, inverse_cube_integral (hx.trans_le hxy) hyT]

private theorem reciprocal_tail_bound {ι : Type*} (s : Finset ι) (height mass : ι → ℝ)
    {x T C : ℝ} (hx : 1 ≤ x) (hxT : x ≤ T) (hC : 0 ≤ C)
    (hheight : ∀ i ∈ s, height i ∈ Icc x T)
    (hcount : ∀ y ∈ Icc x T, (∑ i ∈ s, if height i ≤ y then mass i else 0) ≤
      C * y * Real.log y) :
    (∑ i ∈ s, mass i / height i ^ 2) ≤ 2 * C * ((Real.log x + 1) / x) := by
  classical
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hTpos := hxpos.trans_le hxT
  let f (i : ι) := (Ici (height i)).indicator (fun t : ℝ => mass i * (2 / t ^ 3))
  have hi (i : ι) (_ : i ∈ s) : IntervalIntegrable (f i) volume x T :=
    intervalIntegrable_iff.mpr (((continuousOn_const.mul
      (inverse_cube_continuous hxpos)).intervalIntegrable_of_Icc hxT).def'.indicator
        measurableSet_Ici)
  have hInt :
      (∫ t in x..T, ∑ i ∈ s, f i t) =
        ∑ i ∈ s, mass i * (1 / height i ^ 2 - 1 / T ^ 2) := by
    rw [intervalIntegral.integral_finsetSum hi]
    exact sum_congr rfl fun i hi =>
      restricted_integral hxpos (hheight i hi).1 (hheight i hi).2 (mass i)
  have hCont : ContinuousOn (fun t : ℝ => (2 * C) * (Real.log t / t ^ 2)) (Icc x T) :=
    continuousOn_const.mul ((Real.continuousOn_log.mono fun _ ht =>
      (hxpos.trans_le ht.1).ne').div (continuousOn_id.pow 2) fun _ ht =>
        pow_ne_zero 2 (hxpos.trans_le ht.1).ne')
  have hIntegral :
      (∫ t in x..T, ∑ i ∈ s, f i t) ≤
        (2 * C) * ((Real.log x + 1) / x - (Real.log T + 1) / T) := by
    rw [← log_decay_integral hxpos hxT, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hxT
      (intervalIntegrable_iff.mpr (integrable_finsetSum s fun i h => (hi i h).def')) (hCont.intervalIntegrable_of_Icc hxT) ?_
    intro t ht
    have ht0 : 0 < t := hxpos.trans_le ht.1
    have hEq :
        (∑ i ∈ s, f i t) =
          (∑ i ∈ s, if height i ≤ t then mass i else 0) * (2 / t ^ 3) := by
      rw [sum_mul]
      refine sum_congr rfl ?_
      intro i _
      by_cases h : height i ≤ t <;> simp [f, h]
    rw [hEq]
    calc
      _ ≤ (C * t * Real.log t) * (2 / t ^ 3) :=
        mul_le_mul_of_nonneg_right (hcount t ht) (by positivity)
      _ = _ := by field_simp
  have hEnd := hcount T ⟨hxT, le_rfl⟩
  rw [sum_ite_of_true (fun i hi => (hheight i hi).2)] at hEnd
  have hEnd' : (∑ i ∈ s, mass i) / T ^ 2 ≤ C * Real.log T / T := by
    calc
      _ ≤ (C * T * Real.log T) / T ^ 2 :=
        div_le_div_of_nonneg_right hEnd (sq_nonneg _)
      _ = _ := by field_simp
  have hEq :
      (∑ i ∈ s, mass i / height i ^ 2) =
        (∑ i ∈ s, mass i * (1 / height i ^ 2 - 1 / T ^ 2)) +
          (∑ i ∈ s, mass i) / T ^ 2 := by
    simp_rw [mul_sub, ← div_eq_mul_one_div, sum_sub_distrib, sum_div]
    ring
  rw [hEq]
  rw [hInt] at hIntegral
  have hnon : 0 ≤ C * (Real.log T + 2) / T := by
    have := Real.log_nonneg (hx.trans hxT)
    positivity
  calc
    _ ≤ (2 * C) * ((Real.log x + 1) / x - (Real.log T + 1) / T) +
        C * Real.log T / T := add_le_add hIntegral hEnd'
    _ = 2 * C * ((Real.log x + 1) / x) - C * (Real.log T + 2) / T := by ring
    _ ≤ _ := sub_le_self _ hnon

/-- A cumulative close-pair count bounds the product-weighted mass above a cutoff. -/
theorem weighted_close_pairs_le {J : Type*} (s : Finset (J × J)) (g m w : J → ℝ) {x T C η : ℝ}
    (hx : 2 ≤ x) (hxT : x ≤ T) (hC : 0 ≤ C) (hη : η ≤ x / 2)
    (hg : ∀ i ∈ s, g i.1 ∈ Icc x T ∧ g i.2 ∈ Icc x T)
    (hgap : ∀ i ∈ s, |g i.1 - g i.2| ≤ η)
    (hm : ∀ j, 0 ≤ m j) (hw : ∀ j, 0 ≤ w j)
    (hwm : ∀ j, w j ≤ m j / g j)
    (hcount : ∀ y ∈ Icc x T,
      (∑ i ∈ s, if max (g i.1) (g i.2) ≤ y then m i.1 * m i.2 else 0) ≤
        C * y * Real.log y) :
    let tail := reciprocalLogTail
    (∑ i ∈ s, w i.1 * w i.2) ≤ 4 * C * tail x := by
  dsimp only [reciprocalLogTail]
  classical
  let height (i : J × J) := max (g i.1) (g i.2)
  let mass (i : J × J) := m i.1 * m i.2
  have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 2).trans_le hx
  have hheight (i : J × J) (hi : i ∈ s) : height i ∈ Icc x T :=
    ⟨(hg i hi).1.1.trans (le_max_left _ _), max_le (hg i hi).1.2 (hg i hi).2.2⟩
  have hterm (i : J × J) (hi : i ∈ s) :
      w i.1 * w i.2 ≤ 2 * (mass i / height i ^ 2) := by
    have hp := hg i hi
    have hleft : 0 < g i.1 := hxpos.trans_le hp.1.1
    have hright : 0 < g i.2 := hxpos.trans_le hp.2.1
    have hmass : 0 ≤ mass i := mul_nonneg (hm _) (hm _)
    have hden : height i ^ 2 / 2 ≤ g i.1 * g i.2 := by
      have habs := abs_le.mp (hgap i hi)
      rcases le_total (g i.1) (g i.2) with hle | hle
      · rw [show height i = g i.2 from max_eq_right hle]
        have hh : g i.2 / 2 ≤ g i.1 := by linarith [hp.2.1, habs.1]
        nlinarith [mul_le_mul_of_nonneg_right hh hright.le]
      · rw [show height i = g i.1 from max_eq_left hle]
        have hh : g i.1 / 2 ≤ g i.2 := by linarith [hp.1.1, habs.2]
        nlinarith [mul_le_mul_of_nonneg_left hh hleft.le]
    calc
      _ ≤ (m i.1 / g i.1) * (m i.2 / g i.2) :=
        mul_le_mul (hwm _) (hwm _) (hw _) (div_nonneg (hm _) hleft.le)
      _ = mass i / (g i.1 * g i.2) := (mul_div_mul_comm _ _ _ _).symm
      _ ≤ mass i / (height i ^ 2 / 2) := by
        have hpos : 0 < height i := hxpos.trans_le (hheight i hi).1
        exact div_le_div_of_nonneg_left hmass (by positivity) hden
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, 2 * (mass i / height i ^ 2) := sum_le_sum hterm
    _ = 2 * ∑ i ∈ s, mass i / height i ^ 2 := by rw [mul_sum]
    _ ≤ 2 * (2 * C * ((Real.log x + 1) / x)) :=
      mul_le_mul_of_nonneg_left
        (reciprocal_tail_bound s height mass (one_le_two.trans hx) hxT hC hheight hcount)
        (by norm_num)
    _ = _ := by ring

end D5.S3.Fourier.Concentration.WeightedClosePairTail
