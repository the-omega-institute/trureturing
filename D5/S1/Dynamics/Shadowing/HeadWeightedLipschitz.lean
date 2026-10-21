/- GID: D5/S1/Dynamics/Shadowing/HeadWeightedLipschitz
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/HeadWeightedLipschitz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exact cross-head adjacent-weight criterion for Lipschitz shadowing of full shifts. -/

import D5.S1.Dynamics.Shadowing.HeadWeightedMetric

/-! An exact adjacent-weight criterion for Lipschitz shadowing of head-weight full shifts. -/

open Function Set Filter Topology
open scoped Uniformity

noncomputable section

namespace D5.S1.Dynamics.Shadowing
namespace HeadWeights

/-- A quantitative comparison of arbitrary heads across one depth step. -/
def AdjacentRatioBound (w : HeadWeights) : Prop :=
  ∃ C > 0, ∀ s t n, 1 ≤ n → w.weight s n ≤ C * w.weight t (n - 1)

/-- The diagonal splice has the same strict constant as the cross-head bound.
A diagonal mismatch telescopes to an edge mismatch at a smaller coordinate;
head weights at these different coordinates are then compared quantitatively. -/
theorem diagonal_traces_of_adjacent_ratio (w : HeadWeights) (C : ℝ) (hC : 0 < C)
    (hRatio : ∀ s t n, 1 ≤ n → w.weight s n ≤ C * w.weight t (n - 1))
    {δ : ℝ} (hδ : 0 < δ) (z : ℕ → Space)
    (hz : @MetricPseudoOrbit Space w.rawMetric.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) δ z) :
    @MetricTraces Space w.rawMetric.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) (C * δ) z (diagonalSplice z) := by
  intro i
  classical
  let x := (SymbolicDynamics.FullShift.shift (1 : ℕ))^[i] (diagonalSplice z)
  change w.distance x (z i) < C * δ
  by_cases he : x = z i
  · rw [he, w.distance_self]
    positivity
  let n := PiNat.firstDiff x (z i)
  have hhead : x 0 = z i 0 := by simp [x, shift_one_iterate_apply, diagonalSplice]
  have hn : 1 ≤ n := by
    by_contra hn
    have hnzero : n = 0 := by omega
    exact PiNat.apply_firstDiff_ne he (by simpa only [← hnzero] using hhead)
  have hm : diagonalSplice z (i + n) ≠ z i n := by
    simpa only [x, shift_one_iterate_apply] using PiNat.apply_firstDiff_ne he
  obtain ⟨t, k, _, _, hk, hne⟩ := diagonal_mismatch_edge z i n hm
  have hedge : SymbolicDynamics.FullShift.shift (1 : ℕ) (z t) ≠ z (t + 1) := by
    intro h
    exact hne (by simpa [SymbolicDynamics.FullShift.shift_apply, Nat.add_comm] using congrFun h k)
  let m := PiNat.firstDiff (SymbolicDynamics.FullShift.shift (1 : ℕ) (z t)) (z (t + 1))
  have hmk : m ≤ k := by
    by_contra hmk
    have hh := PiNat.apply_eq_of_lt_firstDiff (Nat.lt_of_not_ge hmk)
    exact hne (by simpa [SymbolicDynamics.FullShift.shift_apply, Nat.add_comm] using hh)
  have hweight : w.weight (x 0) n ≤
      C * w.weight ((SymbolicDynamics.FullShift.shift (1 : ℕ) (z t)) 0) m := by
    exact (hRatio _ _ n hn).trans (mul_le_mul_of_nonneg_left
      (w.antitone _ (show m ≤ n - 1 by omega)) hC.le)
  have ht := hz t
  change w.distance _ _ < δ at ht
  rw [w.distance_of_ne hedge] at ht
  rw [w.distance_of_ne he]
  exact hweight.trans_lt (mul_lt_mul_of_pos_left ht hC)

/-- The adjacent cross-head ratio exactly characterizes Lipschitz shadowing
for every normalized positive nonincreasing head-weight family. -/
theorem rawMetric_hasLipschitzShadowing_iff_adjacent_ratio (w : HeadWeights) :
    @HasLipschitzShadowing Space w.rawMetric.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) ↔ w.AdjacentRatioBound := by
  constructor
  · rintro ⟨L, hL, δ₀, hδ₀, ht⟩
    let C := max (2 * L) (max (2 / δ₀) 1)
    have hC : 0 < C :=
      (show 0 < 2 * L from mul_pos (by norm_num) hL).trans_le (le_max_left _ _)
    have hC_L : 2 * L ≤ C := le_max_left _ _
    have hC_cut : 2 / δ₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have hC_one : 1 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    have hCδ : 2 ≤ C * δ₀ := (div_le_iff₀ hδ₀).mp hC_cut
    have hweight_one (s n : ℕ) : w.weight s n ≤ 1 := by
      simpa only [w.initial] using w.antitone s (Nat.zero_le n)
    refine ⟨C, hC, fun s t n hn => ?_⟩
    by_cases hdepth : n ≤ 1
    · have hn1 : n = 1 := by omega
      subst n
      simpa only [Nat.sub_self, w.initial, mul_one] using
        (hweight_one s 1).trans hC_one
    by_cases hst : s = t
    · subst t
      exact (w.antitone s (Nat.sub_le n 1)).trans
        (le_mul_of_one_le_left (w.positive s (n - 1)).le hC_one)
    by_contra hbound
    have hbig : C * w.weight t (n - 1) < w.weight s n := lt_of_not_ge hbound
    have hsmall : C * w.weight t (n - 1) < 1 := hbig.trans_le (hweight_one s n)
    let δ := 2 * w.weight t (n - 1)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact mul_pos (by norm_num) (w.positive t (n - 1))
    have hδcut : δ ≤ δ₀ := by
      have hscaled : C * (2 * w.weight t (n - 1)) < C * δ₀ := by
        nlinarith only [hsmall, hCδ]
      exact ((mul_lt_mul_iff_right₀ hC).mp hscaled).le
    have hscale : L * δ ≤ w.weight s n := by
      calc
        L * δ = (2 * L) * w.weight t (n - 1) := by dsimp [δ]; ring
        _ ≤ C * w.weight t (n - 1) :=
          mul_le_mul_of_nonneg_right hC_L (w.positive t (n - 1)).le
        _ ≤ w.weight s n := hbig.le
    have hpo : @MetricPseudoOrbit Space w.rawMetric.toPseudoMetricSpace
        (SymbolicDynamics.FullShift.shift (1 : ℕ)) δ (defectOrbit s t n) := by
      apply w.defect_pseudoOrbit s t n hst
      dsimp [δ]
      linarith [w.positive t (n - 1)]
    obtain ⟨y, hy⟩ := ht δ hδ hδcut (defectOrbit s t n) hpo
    exact w.defect_no_tracer s t n hst (by omega) hscale y hy
  · rintro ⟨C, hC, hRatio⟩
    refine ⟨C, hC, 1, by norm_num, fun δ hδ _ z hz => ?_⟩
    exact ⟨diagonalSplice z, w.diagonal_traces_of_adjacent_ratio C hC hRatio hδ z hz⟩


#print axioms diagonal_traces_of_adjacent_ratio
#print axioms rawMetric_hasLipschitzShadowing_iff_adjacent_ratio

end HeadWeights
end D5.S1.Dynamics.Shadowing
