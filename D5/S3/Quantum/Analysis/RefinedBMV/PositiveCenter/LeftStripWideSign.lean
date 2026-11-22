/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripWideSign
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripWideSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict negativity of the mixed derivative of the original kernel through gap one. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripWideBounds

/-! Strict sign on the left strip for endpoint gaps through one. -/

namespace RefinedBMV.PositiveCenter

open private Endpoints InInterval lowerHalf upperHalf leftStripRegularizedIntegrand_pos from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripLowSign
open private wideCheckCover wideCheckCover_sound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripWideBounds
open private leftStripRegularizedIntegrand leftStripScaledIntegrand leftStripReflectedSlope
  leftStrip_small_slope leftStrip_scaled_integrand_eq_regularized leftStrip_weightedThird_eq
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripCollision
open private leftStrip_logKernel_mixed_lt_of_weighted from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripKernel

noncomputable section

private theorem wideCheckCover_of_children (n : ℕ) (H A V : Endpoints)
    (h : (if (n + 1) % 3 = 0 then
          wideCheckCover n H (lowerHalf A) V && wideCheckCover n H (upperHalf A) V
        else if (n + 1) % 3 = 2 then
          wideCheckCover n H A (lowerHalf V) && wideCheckCover n H A (upperHalf V)
        else
          wideCheckCover n (lowerHalf H) A D && wideCheckCover n (upperHalf H) A D) = true) :
    wideCheckCover (n + 1) H A V = true := by
  rw [wideCheckCover]
  split
  · rfl
  · exact h

local macro "splitCover" : tactic =>
  `(tactic| (
    apply wideCheckCover_of_children
    simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ite_true, ite_false]
    apply Bool.and_eq_true_iff.mpr
    constructor))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem check_upper_one_to_five_quarters :
    wideCheckCover 11 (0, 3 / 11) (0, 1 / 2) (1, 5 / 4) = true := by
  iterate 3 all_goals splitCover
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem check_upper_five_quarters_to_three_halves :
    wideCheckCover 11 (0, 3 / 11) (0, 1 / 2) (5 / 4, 3 / 2) = true := by
  iterate 3 all_goals splitCover
  all_goals decide +kernel

private theorem leftStripRegularizedIntegrand_pos_wide {p : ℕ} (hp : 11 ≤ p)
    {a v : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1 / 2) (hd : 0 < v - a) (hv : v ≤ 3 / 2) :
    0 < leftStripRegularizedIntegrand p a v := by
  by_cases hvlow : v ≤ 1
  · exact leftStripRegularizedIntegrand_pos hp ha ha₁ hd hvlow
  have hp₀ : 0 < p := by omega
  have hh : InInterval (0, 3 / 11) (3 / (p : ℝ)) := by
    constructor
    · push_cast
      positivity
    · norm_num
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have ha' : InInterval (0, 1 / 2) a := ⟨by simpa using ha, by simpa using ha₁⟩
  have hc := wideCheckCover_sound hp₀ ha hd.le hv 11 (0, 3 / 11) (0, 1 / 2)
  rcases le_total v (5 / 4) with h | h
  · exact hc _ hh ha' ⟨by simpa using le_of_not_ge hvlow, by simpa using h⟩
      check_upper_one_to_five_quarters
  · exact hc _ hh ha' ⟨by simpa using h, by simpa using hv⟩
      check_upper_five_quarters_to_three_halves

/-- The exact logarithmic kernel has strictly negative mixed derivative through endpoint gap
`1` on the left strip. -/
theorem leftStrip_logKernel_mixed_lt_gap_one {p : ℕ} (hp : 11 ≤ p)
    {u v : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v) (hd : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have hv := hu.trans huv
  refine leftStrip_logKernel_mixed_lt_of_weighted hp₀ hu huv
    (leftStrip_small_slope hp hu hu₁) ?_
  dsimp only
  intro a ha
  have hav := ha.2.trans huv
  have hsign : 0 < leftStripScaledIntegrand p a v := by
    rw [leftStrip_scaled_integrand_eq_regularized hp₀ hv hav]
    exact leftStripRegularizedIntegrand_pos_wide hp ha.1.le (ha.2.le.trans hu₁)
      (sub_pos.mpr hav) (by linarith only [hd, hu₁])
  have he := leftStrip_weightedThird_eq (γ := leftStripReflectedSlope p v) hp₀ hv hav
  exact he.trans_lt (sub_neg.mpr (lt_of_sub_pos ((mul_pos_iff_of_pos_left hv).mp hsign)))

#print axioms leftStrip_logKernel_mixed_lt_gap_one

end

end RefinedBMV.PositiveCenter
