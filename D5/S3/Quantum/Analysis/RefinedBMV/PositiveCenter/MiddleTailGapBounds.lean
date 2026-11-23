/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailGapBounds
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Keep the joint dependence of gap slope and exponential decay on the central strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailMarginalBound

/-! Bounds for replacing the gap coordinate by its slope in the joint mixed score. -/

open Set

namespace RefinedBMV.PositiveCenter

private theorem exp_gap_ratio_le_quadratic {z : ℝ} (hz : 0 < z) :
    z / (Real.exp z - 1) ≤ 1 - z / 2 + z ^ 2 / 12 := by
  let B := 1 - z / 2 + z ^ 2 / 12
  have hB : 0 ≤ B := by dsimp only [B]; nlinarith only [sq_nonneg (z - 3)]
  have hTaylor := Real.sum_le_exp_of_nonneg hz.le 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hTaylor
  have hT : z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120 ≤ Real.exp z - 1 := by
    linarith only [hTaylor]
  have hrem : 0 ≤ z ^ 5 * (2 - z + z ^ 2) / 1440 := by
    have hP : 0 ≤ 2 - z + z ^ 2 := by nlinarith only [sq_nonneg (z - 1 / 2)]
    exact div_nonneg (mul_nonneg (pow_nonneg hz.le _) hP) (by norm_num)
  have hpos : 0 < Real.exp z - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hz)
  apply (div_le_iff₀ hpos).2
  calc
    z ≤ B * (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120) := by
      dsimp only [B]
      nlinarith only [hrem]
    _ ≤ B * (Real.exp z - 1) := mul_le_mul_of_nonneg_left hT hB

private theorem exp_neg_thirteen_fourths_ge : (31 / 800 : ℝ) ≤ Real.exp (-(13 / 4)) := by
  have hE := Real.exp_bound' (x := (13 : ℝ) / 16) (n := 12)
    (by norm_num) (by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hE
  have hsmall : Real.exp ((13 : ℝ) / 16) ≤ 2817 / 1250 := hE.trans (by norm_num)
  have hlarge : Real.exp ((13 : ℝ) / 4) ≤ 800 / 31 := by
    calc
      _ = Real.exp ((13 : ℝ) / 16) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2817 / 1250 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos _).le hsmall _
      _ ≤ _ := by norm_num
  rw [Real.exp_neg]
  have hinv := inv_anti₀ (Real.exp_pos ((13 : ℝ) / 4)) hlarge
  simpa only [inv_div, inv_inv] using hinv

/-- On the central upper gap band both the slope cutoff and the exponential
decay can be expressed in terms of the gap slope. -/
theorem middleTail_gap_bounds {h d : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hd₀ : 13 / 4 ≤ d) (hd₁ : d ≤ 7 / 2) :
    let q := upperTailSlope h d
    let Q := (4 : ℝ) / 13 - h / 2 + 13 * h ^ 2 / 48
    0 < q ∧ q ≤ Q ∧ Q ≤ 4 / 13 ∧
      (31 / 800 : ℝ) * (13 / 4) ^ 4 * q ^ 4 ≤ Real.exp (-d) := by
  intro q Q
  have hd : 0 < d := (by norm_num : (0 : ℝ) < 13 / 4).trans_le hd₀
  obtain ⟨hq, hqle, _⟩ := upperTailSlope_bounds hh hd
  have hle₀ : q ≤ upperTailSlope h (13 / 4) := by
    change h / (Real.exp (h * d) - 1) ≤ h / (Real.exp (h * (13 / 4)) - 1)
    apply div_le_div_of_nonneg_left hh.le
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh (by norm_num))))
    gcongr
  let z := h * (13 / 4)
  have hz : 0 < z := by dsimp only [z]; positivity
  have hEq : upperTailSlope h (13 / 4) = (4 / 13) * (z / (Real.exp z - 1)) := by
    unfold upperTailSlope
    change h / (Real.exp z - 1) = _
    rw [← mul_div_assoc]
    congr 1
    dsimp only [z]
    ring
  have hbound : upperTailSlope h (13 / 4) ≤ Q := by
    rw [hEq]
    have H := mul_le_mul_of_nonneg_left (exp_gap_ratio_le_quadratic hz)
      (by norm_num : (0 : ℝ) ≤ 4 / 13)
    dsimp only [Q, z] at *
    nlinarith only [H]
  have hQ : Q ≤ 4 / 13 := by
    dsimp only [Q]
    nlinarith only [mul_nonneg hh.le (sub_nonneg.mpr hhmax), hh]
  let F : ℝ → ℝ := fun t ↦ t ^ 4 * Real.exp (-t)
  have hDeriv (t : ℝ) : HasDerivAt F (t ^ 3 * Real.exp (-t) * (4 - t)) t := by
    refine (((hasDerivAt_id' t).pow 4).mul (hasDerivAt_id' t).neg.exp).congr_deriv ?_
    simp only [Pi.neg_apply, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat]
    ring
  have hmono : MonotoneOn F (Icc (13 / 4 : ℝ) (7 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t _ ↦ (hDeriv t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hDeriv t).differentiableAt.differentiableWithinAt)
    intro t ht
    obtain ⟨hlo, hhi⟩ := interior_subset ht
    rw [(hDeriv t).deriv]
    have h₁ : 0 ≤ t := by linarith only [hlo]
    have h₂ : 0 ≤ 4 - t := by linarith only [hhi]
    positivity
  have hF := hmono (show (13 / 4 : ℝ) ∈ Icc (13 / 4 : ℝ) (7 / 2) from ⟨le_rfl, by norm_num⟩)
    (show d ∈ Icc (13 / 4 : ℝ) (7 / 2) from ⟨hd₀, hd₁⟩) hd₀
  have hq' : q * d ≤ 1 := by
    simpa only [one_div] using (le_div_iff₀ hd).mp hqle
  have hqpow : q ^ 4 * d ^ 4 ≤ 1 := by
    rw [← mul_pow, ← one_pow (n := 4)]
    exact pow_le_pow_left₀ (mul_nonneg hq.le hd.le) hq' _
  refine ⟨hq, hle₀.trans hbound, hQ, ?_⟩
  apply (le_of_mul_le_mul_right ?_ (pow_pos hd 4))
  calc
    _ = ((31 / 800 : ℝ) * (13 / 4) ^ 4) * (q ^ 4 * d ^ 4) := by ring
    _ ≤ ((31 / 800 : ℝ) * (13 / 4) ^ 4) * 1 :=
      mul_le_mul_of_nonneg_left hqpow (by norm_num)
    _ ≤ F (13 / 4) := by
      dsimp only [F]
      rw [mul_one, mul_comm (31 / 800 : ℝ)]
      exact mul_le_mul_of_nonneg_left exp_neg_thirteen_fourths_ge (by norm_num)
    _ ≤ F d := hF
    _ = _ := by dsimp only [F]; ring

end RefinedBMV.PositiveCenter
