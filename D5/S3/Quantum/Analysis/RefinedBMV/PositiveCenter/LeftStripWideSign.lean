/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripWideSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict left-strip sign through endpoint gap one. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripLowSign

/-! The left-strip interval replay for the additional integration gaps. -/

open Set

namespace RefinedBMV.PositiveCenter

open private checkCover checkCover_sound Endpoints InInterval
  lowerHalf upperHalf marginalLimit jointLimit from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripLowSign
open private leftStrip_logKernel_mixed_lt_of_weighted leftStrip_small_slope weightedThird from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripKernel

noncomputable section

private theorem checkCover_of_children (n : ℕ) (H A D : Endpoints)
    (h : (if (n + 1) % 3 = 0 then
          checkCover true n H (lowerHalf A) D && checkCover true n H (upperHalf A) D
        else if (n + 1) % 3 = 2 then
          checkCover true n H A (lowerHalf D) && checkCover true n H A (upperHalf D)
        else
          checkCover true n (lowerHalf H) A D && checkCover true n (upperHalf H) A D) = true) :
    checkCover true (n + 1) H A D = true := by
  rw [checkCover]
  split
  · rfl
  · exact h

local macro "splitCover" : tactic =>
  `(tactic| (
    apply checkCover_of_children
    simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ite_true, ite_false]
    apply Bool.and_eq_true_iff.mpr
    constructor))

set_option maxHeartbeats 0 in
-- Reduce the closed interval checks in separate kernel declarations.
set_option maxRecDepth 20000 in
private theorem check_gap_one_to_five_quarters :
    checkCover true 15 (0, 3 / 11) (0, 1 / 2) (1, 5 / 4) = true := by
  iterate 3 all_goals splitCover
  all_goals decide +kernel

set_option maxHeartbeats 0 in
-- Reduce the closed interval checks in separate kernel declarations.
set_option maxRecDepth 20000 in
private theorem check_gap_five_quarters_to_three_halves :
    checkCover true 16 (0, 3 / 11) (0, 1 / 2) (5 / 4, 3 / 2) = true := by
  iterate 6 all_goals splitCover
  all_goals decide +kernel

/-- The regularized integrand is strictly positive through integration gap `3/2`. -/
theorem leftStripRegularizedIntegrand_pos_three_halves {p : ℕ} (hp : 11 ≤ p)
    {a v : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1 / 2) (hd : 0 < v - a) (hd₁ : v - a ≤ 3 / 2) :
    0 < leftStripRegularizedIntegrand p a v := by
  by_cases hdsmall : v - a ≤ 1
  · exact leftStripRegularizedIntegrand_pos hp ha ha₁ hd hdsmall
  have hp₀ : 0 < p := by omega
  have hh : InInterval (0, 3 / 11) (3 / (p : ℝ)) := by
    constructor
    · push_cast
      positivity
    · norm_num
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have ha' : InInterval (0, 1 / 2) a := ⟨by simpa using ha, by simpa using ha₁⟩
  have hD : v - a ≤ (marginalLimit true 2 : ℝ) := by simpa [marginalLimit] using hd₁
  have hV : v ≤ (jointLimit true : ℝ) := by
    norm_num [jointLimit]
    linarith
  rcases le_total (v - a) (5 / 4) with h | h
  · exact checkCover_sound true hp₀ ha hd.le hD hV 15 _ _ _ hh ha'
      ⟨by simpa using (le_of_not_ge hdsmall), by simpa using h⟩ check_gap_one_to_five_quarters
  · exact checkCover_sound true hp₀ ha hd.le hD hV 16 _ _ _ hh ha'
      ⟨by simpa using h, by simpa using hd₁⟩ check_gap_five_quarters_to_three_halves

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
    exact leftStripRegularizedIntegrand_pos_three_halves hp ha.1.le (ha.2.le.trans hu₁)
      (sub_pos.mpr hav) (by linarith only [hd, hu₁, ha.1])
  have he := leftStrip_weightedThird_eq (γ := leftStripReflectedSlope p v) hp₀ hv hav
  exact he.trans_lt (sub_neg.mpr (lt_of_sub_pos ((mul_pos_iff_of_pos_left hv).mp hsign)))

#print axioms leftStripRegularizedIntegrand_pos_three_halves
#print axioms leftStrip_logKernel_mixed_lt_gap_one

end

end RefinedBMV.PositiveCenter
