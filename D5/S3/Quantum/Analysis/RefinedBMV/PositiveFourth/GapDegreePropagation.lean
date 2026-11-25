/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/GapDegreePropagation
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree monotonicity of the four-copy defect with a unit spectral node. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation
import D5.S3.Quantum.Analysis.RefinedBMVUniformThreeSpectrum

/-! Increasing the degree of a four-slot homogeneous defect multiplies
its lower bound by any one of the spectral nodes. -/

open scoped BigOperators

namespace RefinedBMV.FourCopyGap

open DividedDifference (homogeneousThree homogeneousTwo defect_eq_homogeneous)
open private monomial balanced sum_gaps_nested from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private gapDefect_scale from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation

private theorem unit_slot_sum_succ (p : ℕ) (a b c : ℝ) :
    (∑ g ∈ gaps (p + 1), monomial 1 a b c g) =
      homogeneousThree (p + 1) a b c + ∑ g ∈ gaps p, monomial 1 a b c g := by
  rw [← Finset.sum_filter_add_sum_filter_not (gaps (p + 1)) (fun g : Gap => g.1 = 0)]
  congr 1
  · rw [Finset.sum_filter, sum_gaps_nested]
    rw [Finset.sum_eq_single 0]
    · simp [homogeneousThree, homogeneousTwo, monomial, Finset.mul_sum, mul_assoc]
    · intro i _ hi
      simp [hi]
    · simp
  · refine Finset.sum_nbij' (fun g : Gap => (g.1 - 1, g.2))
      (fun g : Gap => (g.1 + 1, g.2)) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, mem_gaps] at hg
      simp only [mem_gaps]
      omega
    · intro g hg
      simp only [mem_gaps] at hg
      simp only [Finset.mem_filter, mem_gaps]
      omega
    · intro g hg
      have hg₁ : g.1 ≠ 0 := (Finset.mem_filter.mp hg).2
      rcases g with ⟨i, j, k, l⟩
      change (i - 1 + 1, j, k, l) = (i, j, k, l)
      have hi : i - 1 + 1 = i := by omega
      rw [hi]
    · rintro ⟨i, j, k, l⟩ _
      simp
    · intro g _
      simp [monomial]

private theorem homogeneousThree_ge (p : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ((p + 2).choose 2 : ℝ) * (a * b * c) ^ ((p : ℝ) / 3) ≤
      homogeneousThree p a b c := by
  let root (x : ℝ) := x ^ (1 / 3 : ℝ)
  have cube (x : ℝ) (hx : 0 ≤ x) : (root x) ^ 3 = x := by
    dsimp [root]
    rw [← Real.rpow_mul_natCast hx]
    norm_num
  have h := UniformThreeSpectrum.defect_nonneg_all p (root a) (root b) (root c)
    (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _) (Real.rpow_nonneg hc _)
  rw [defect_eq_homogeneous, cube a ha, cube b hb, cube c hc] at h
  dsimp [root] at h
  rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (mul_nonneg ha hb) hc,
    ← Real.rpow_mul_natCast (by positivity),
    show (1 / 3 : ℝ) * (p : ℝ) = (p : ℝ) / 3 by ring] at h
  exact sub_nonneg.mp h

/-- A four-slot defect with a unit node grows with the word degree. -/
theorem gapDefect_unit_le_succ (p : ℕ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    gapDefect p 1 a b c ≤ gapDefect (p + 1) 1 a b c := by
  let g := (a * b * c) ^ (1 / 4 : ℝ)
  have hprod : 0 ≤ a * b * c := by positivity
  have hg : 0 ≤ g := Real.rpow_nonneg hprod _
  have hbal (n : ℕ) : balanced n 1 a b c = g ^ n := by
    unfold balanced
    rw [Real.one_rpow, one_mul, ← Real.mul_rpow ha hb,
      ← Real.mul_rpow (mul_nonneg ha hb) hc]
    dsimp [g]
    rw [← Real.rpow_mul_natCast hprod]
    congr 1
    ring
  have hgeom :
      (a * b * c) ^ (((p + 1 : ℕ) : ℝ) / 3) =
        g ^ p * g ^ (((p : ℝ) + 4) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add_of_nonneg hg (by positivity) (by positivity)]
    dsimp [g]
    rw [← Real.rpow_mul hprod]
    congr 1
    push_cast
    ring
  have hbound := homogeneousThree_ge (p + 1) ha hb hc
  rw [hgeom] at hbound
  have hp : 0 ≤ (p : ℝ) := by positivity
  have htangent := one_add_mul_self_le_rpow_one_add
    (s := g - 1) (p := ((p : ℝ) + 4) / 3) (by linarith) (by linarith)
  rw [show 1 + (g - 1) = g by ring] at htangent
  have hchoose (r : ℕ) :
      ((p + 3).choose r : ℝ) * (p + 4 : ℝ) =
        ((p + 4).choose r : ℝ) * ((p + 4 - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq (p + 3) r
  have hstep : ((p + 4).choose 3 : ℝ) * (p + 1 : ℝ) =
      ((p + 3).choose 3 : ℝ) * (p + 4 : ℝ) := by
    have h := hchoose 3
    rw [show p + 4 - 3 = p + 1 by omega] at h
    push_cast at h
    exact h.symm
  have hcount : ((p + 3).choose 2 : ℝ) * (p + 1 : ℝ) =
      3 * ((p + 3).choose 3 : ℝ) := by
    have h : (p + 3).choose 3 * 3 = (p + 3).choose 2 * (p + 1) := by
      exact Nat.choose_succ_right_eq (p + 3) 2
    exact_mod_cast (show (p + 3).choose 2 * (p + 1) =
      3 * (p + 3).choose 3 by simpa only [mul_comm] using h.symm)
  rw [gapDefect, gapDefect, hbal, hbal, unit_slot_sum_succ, gaps_card, gaps_card]
  have hcand : ((p + 4).choose 3 : ℝ) * g ^ (p + 1) -
      ((p + 3).choose 3 : ℝ) * g ^ p ≤ homogeneousThree (p + 1) a b c := by
    apply le_of_mul_le_mul_left ?_ (show 0 < (p : ℝ) + 1 by positivity)
    have hresult := mul_le_mul_of_nonneg_left htangent
      (show 0 ≤ 3 * ((p + 3).choose 3 : ℝ) * g ^ p by positivity)
    have hraw := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (p : ℝ) + 1 by positivity)
    rw [pow_succ]
    linear_combination hraw + hresult + (g ^ p * g) * hstep -
      (g ^ p * g ^ (((p : ℝ) + 4) / 3)) * hcount
  linarith

/-- One factor of any chosen positive node is a lower bound for the
successive-degree growth of the unnormalized four-slot defect. -/
theorem mul_gapDefect_le_succ (p : ℕ) {z a b c : ℝ} (hz : 0 < z)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    z * gapDefect p z a b c ≤ gapDefect (p + 1) z a b c := by
  have ha' := div_nonneg ha hz.le
  have hb' := div_nonneg hb hz.le
  have hc' := div_nonneg hc hz.le
  have scale (n : ℕ) :
      gapDefect n z a b c = z ^ n * gapDefect n 1 (a/z) (b/z) (c/z) := by
    simpa only [mul_one, one_mul, mul_div_cancel₀ _ hz.ne', mul_comm z] using
      (gapDefect_scale n hz.le zero_le_one ha' hb' hc')
  rw [scale p, scale (p + 1), pow_succ, ← mul_assoc, mul_comm z (z ^ p)]
  exact mul_le_mul_of_nonneg_left
    (gapDefect_unit_le_succ p ha' hb' hc') (by positivity)

#print axioms mul_gapDefect_le_succ

end RefinedBMV.FourCopyGap
