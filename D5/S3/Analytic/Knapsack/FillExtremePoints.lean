/- GID: D5/S3/Analytic/Knapsack/FillExtremePoints
   generality: G
   mirror-B: D5/B/S3/Analytic/Knapsack/FillExtremePoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every extreme feasible fill has at most one strictly fractional coordinate. -/

import D5.S3.Analytic.Knapsack.GridDualStructure
import Mathlib.Analysis.Convex.Extreme

open Set
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Knapsack.FillExtremePoints

open GridDualStructure (FillFeasible)

variable {ι : Type*} [Fintype ι]

/-- An extreme feasible fill cannot have two distinct strictly fractional coordinates. -/
theorem extreme_fill_at_most_one_fractional (c d : ι → ℝ) (M : ℝ) (a : ι → ℝ)
    (_hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i)
    (ha : a ∈ extremePoints ℝ {b | FillFeasible c d M b}) :
    ¬ ∃ i j, i ≠ j ∧ a i ∈ Ioo 0 1 ∧ a j ∈ Ioo 0 1 := by
  classical
  rintro ⟨i, j, hij, hi, hj⟩
  let w := fun k => d k - c k
  have hw (k : ι) : 0 < w k := sub_pos.mpr (hcd k)
  let δ := min (min (w i * a i) (w i * (1 - a i)))
    (min (w j * a j) (w j * (1 - a j)))
  have hδ : 0 < δ := lt_min
    (lt_min (mul_pos (hw i) hi.1) (mul_pos (hw i) (sub_pos.mpr hi.2)))
    (lt_min (mul_pos (hw j) hj.1) (mul_pos (hw j) (sub_pos.mpr hj.2)))
  have hδi : δ ≤ w i * a i :=
    (min_le_left (min (w i * a i) (w i * (1 - a i)))
      (min (w j * a j) (w j * (1 - a j)))).trans (min_le_left _ _)
  have hδi' : δ ≤ w i * (1 - a i) :=
    (min_le_left (min (w i * a i) (w i * (1 - a i)))
      (min (w j * a j) (w j * (1 - a j)))).trans (min_le_right _ _)
  have hδj : δ ≤ w j * a j :=
    (min_le_right (min (w i * a i) (w i * (1 - a i)))
      (min (w j * a j) (w j * (1 - a j)))).trans (min_le_left _ _)
  have hδj' : δ ≤ w j * (1 - a j) :=
    (min_le_right (min (w i * a i) (w i * (1 - a i)))
      (min (w j * a j) (w j * (1 - a j)))).trans (min_le_right _ _)
  have hdi : δ / w i ≤ a i :=
    (div_le_iff₀ (hw i)).mpr (by simpa only [mul_comm] using hδi)
  have hdi' : δ / w i ≤ 1 - a i :=
    (div_le_iff₀ (hw i)).mpr (by simpa only [mul_comm] using hδi')
  have hdj : δ / w j ≤ a j :=
    (div_le_iff₀ (hw j)).mpr (by simpa only [mul_comm] using hδj)
  have hdj' : δ / w j ≤ 1 - a j :=
    (div_le_iff₀ (hw j)).mpr (by simpa only [mul_comm] using hδj')
  let e := fun k => (if k = i then δ / w i else 0) - (if k = j then δ / w j else 0)
  have hsum : (∑ k, w k * e k) = 0 := by
    simp [e, mul_sub, mul_ite, Finset.sum_sub_distrib,
      mul_div_cancel₀ δ (hw i).ne', mul_div_cancel₀ δ (hw j).ne']
  have hfeas : FillFeasible c d M a := (mem_extremePoints_iff_left.mp ha).1
  have hbox (k : ι) : a k + e k ∈ Icc 0 1 ∧ a k - e k ∈ Icc 0 1 := by
    by_cases hki : k = i
    · subst k
      simp only [e, if_pos, if_neg hij, sub_zero, mem_Icc]
      have hpos := (div_pos hδ (hw i)).le
      have hbounds := hfeas.1 i
      exact ⟨⟨by linarith [hbounds.1], by linarith⟩,
        ⟨by linarith, by linarith [hbounds.2]⟩⟩
    · by_cases hkj : k = j
      · subst k
        simp only [e, if_neg hki, if_pos, zero_sub, mem_Icc]
        have hpos := (div_pos hδ (hw j)).le
        have hbounds := hfeas.1 j
        exact ⟨⟨by linarith, by linarith [hbounds.2]⟩,
          ⟨by linarith [hbounds.1], by linarith⟩⟩
      · simpa [e, hki, hkj] using And.intro (hfeas.1 k) (hfeas.1 k)
  have hplus : FillFeasible c d M (a + e) := by
    refine ⟨fun k => (hbox k).1, ?_⟩
    change (∑ k, w k * (a k + e k)) ≤ M - ∑ k, c k
    simpa only [mul_add, Finset.sum_add_distrib, hsum, add_zero] using hfeas.2
  have hminus : FillFeasible c d M (a - e) := by
    refine ⟨fun k => (hbox k).2, ?_⟩
    change (∑ k, w k * (a k - e k)) ≤ M - ∑ k, c k
    simpa only [mul_sub, Finset.sum_sub_distrib, hsum, sub_zero] using hfeas.2
  have heq := (mem_extremePoints_iff_left.mp ha).2 (a + e) hplus (a - e) hminus
    (mem_openSegment_add_sub (𝕜 := ℝ) a e)
  have hei := congrFun heq i
  simp only [Pi.add_apply, e, if_pos, if_neg hij, sub_zero] at hei
  linarith [div_pos hδ (hw i)]

#print axioms extreme_fill_at_most_one_fractional

end D5.S3.Analytic.Knapsack.FillExtremePoints
