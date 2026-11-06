/- GID: D5/S3/Arith/Robin/PriceRecord/NonlinearPrimeExclusion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/NonlinearPrimeExclusion
   mirror-E: none(waiver:nonlinear-real-root-construction)
   anchors: []
   utility: none
   digest: Nonlinear deletion and insertion barriers for the same original Robin minimum. -/

import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion

open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.RestrictedDivisorStrictInventory
open D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand

/-- The exact one-layer deletion barrier. -/
def deletionBarrier (L x : ℝ) : ℝ := L - L ^ (x / (x + 1)) - Real.log x

/-- The exact fresh-prime insertion barrier. -/
def insertionBarrier (L x : ℝ) : ℝ := Real.log x - L ^ (1 + 1 / x) + L

private theorem deletion_strictAnti {L : ℝ} (hL : 1 < L) :
    StrictAntiOn (deletionBarrier L) (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by change 1 < x at hx; linarith
  have hy0 : 0 < y := by change 1 < y at hy; linarith
  have hr : x / (x + 1) < y / (y + 1) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hp := Real.rpow_lt_rpow_of_exponent_lt hL hr
  have hl := Real.log_lt_log hx0 hxy
  dsimp [deletionBarrier]
  linarith

private theorem insertion_strictMono {L : ℝ} (hL : 1 < L) :
    StrictMonoOn (insertionBarrier L) (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by change 1 < x at hx; linarith
  have hr : 1 + 1 / y < 1 + 1 / x := by
    linarith only [one_div_lt_one_div_of_lt hx0 hxy]
  have hp := Real.rpow_lt_rpow_of_exponent_lt hL hr
  have hl := Real.log_lt_log hx0 hxy
  dsimp [insertionBarrier]
  linarith

private theorem loglog_comparison {L y c : ℝ} (hL : 1 < L) (hy : 1 < y)
    (hc : 0 < c) :
    Real.log (Real.log L) - Real.log (Real.log y) ≤ Real.log c ↔
      L ^ (1 / c) ≤ y := by
  have hL0 : 0 < L := by linarith
  have hy0 : 0 < y := by linarith
  have hlL := Real.log_pos hL
  have hly := Real.log_pos hy
  rw [← Real.log_div hlL.ne' hly.ne',
    Real.log_le_log_iff (div_pos hlL hly) hc, div_le_iff₀ hly]
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) hy0,
    Real.log_rpow hL0]
  have he : Real.log L * (1 / c) = Real.log L / c := by ring
  rw [he, div_le_iff₀ hc]
  constructor <;> intro h <;> nlinarith only [h]

private theorem deletion_test {L x : ℝ} (hL : 1 < L) (hx : 1 < x)
    (hy : 1 < L - Real.log x) :
    0 ≤ deletionBarrier L x ↔
      Real.log (Real.log L) - Real.log (Real.log (L - Real.log x)) ≤
        Real.log (1 + 1 / x) := by
  have hx0 : 0 < x := by linarith
  have he : 1 / (1 + 1 / x) = x / (x + 1) := by field_simp
  rw [loglog_comparison hL hy (by positivity), he]
  dsimp [deletionBarrier]
  constructor <;> intro h <;> linarith

private theorem insertion_test {L x : ℝ} (hL : 1 < L) (hx : 1 < x) :
    0 ≤ insertionBarrier L x ↔
      Real.log (1 + 1 / x) ≤
        Real.log (Real.log (L + Real.log x)) - Real.log (Real.log L) := by
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hlx := Real.log_pos hx
  have hy : 1 < L + Real.log x := by linarith
  have hc : 0 < 1 + 1 / x := by positivity
  rw [← Real.log_div (Real.log_pos hy).ne' (Real.log_pos hL).ne',
    Real.log_le_log_iff hc (div_pos (Real.log_pos hy) (Real.log_pos hL)),
    le_div_iff₀ (Real.log_pos hL)]
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hL0 _) (by linarith : 0 < L + Real.log x),
    Real.log_rpow hL0]
  dsimp [insertionBarrier]
  constructor <;> intro h <;> nlinarith only [h]

private theorem deletion_half_pos {L : ℝ} (hL : 16 < L) :
    0 < deletionBarrier L (L / 2) := by
  have hL0 : 0 < L := by linarith
  have hl := Real.log_pos (by linarith : 1 < L)
  have hlog16 : Real.log (16 : ℝ) ≤ 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2 ⊢
    linarith
  have hb := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num : (0 : ℝ) < 16))
  rw [Real.log_div hL0.ne' (by norm_num : (16 : ℝ) ≠ 0)] at hb
  have hsmall : 2 + 2 * Real.log L < L := by linarith
  let v := 2 * Real.log L / (L + 2)
  have hv : 0 < v := div_pos (by positivity) (by linarith)
  have hexp : 1 + v < Real.exp v := by linarith only [Real.add_one_lt_exp hv.ne']
  have hinv : Real.exp (-v) < 1 / (1 + v) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by linarith) hexp
  have hnorm : L - L / (1 + v) > Real.log L := by
    apply (lt_sub_iff_add_lt).mpr
    apply (add_lt_iff_lt_sub_left).mpr
    apply (div_lt_iff₀ (by linarith : 0 < 1 + v)).mpr
    dsimp [v]
    field_simp
    nlinarith [mul_pos hl (show 0 < L - (2 + 2 * Real.log L) by linarith)]
  have hp : L ^ ((L / 2) / (L / 2 + 1)) = L * Real.exp (-v) := by
    rw [Real.rpow_def_of_pos hL0, ← Real.exp_log hL0, ← Real.exp_add]
    congr 1
    dsimp [v]
    field_simp
    ring
  have hloghalf : Real.log (L / 2) < Real.log L :=
    Real.log_lt_log (by positivity) (by linarith)
  dsimp [deletionBarrier]
  rw [hp]
  have hm := mul_lt_mul_of_pos_left hinv hL0
  linarith

private theorem deletion_cutoff_neg {L z : ℝ} (hL : 16 < L) (hz : 11 < z)
    (hzL : z < L) (hroot : firstLayerPrice z = 1 / (L * Real.log L)) :
    deletionBarrier L z < 0 := by
  have hL1 : 1 < L := by linarith
  have hz1 : 1 < z := by linarith
  have hlz := Real.log_pos hz1
  have hy : 1 < L - Real.log z := by
    have hlog := Real.log_lt_sub_one_of_pos (by linarith : 0 < L) (by linarith : L ≠ 1)
    have hmono := Real.log_lt_log (by linarith : 0 < z) hzL
    linarith
  have hprice : Real.log (1 + 1 / z) = Real.log z / (L * Real.log L) := by
    change Real.log (1 + 1 / z) / Real.log z = _ at hroot
    exact (div_eq_iff hlz.ne').mp hroot |>.trans (by ring)
  have ht := loglog_tangent hL1 hy (by linarith : L ≠ L - Real.log z)
  change _ < (L - Real.log z - L) * (1 / (L * Real.log L)) at ht
  have hstrict : Real.log (1 + 1 / z) <
      Real.log (Real.log L) - Real.log (Real.log (L - Real.log z)) := by
    rw [hprice]
    nlinarith only [ht]
  by_contra hn
  have htest := (deletion_test hL1 hz1 hy).mp (le_of_not_gt hn)
  linarith

private theorem insertion_at_clock_neg {L : ℝ} (hL : 1 < L) :
    insertionBarrier L L < 0 := by
  have hL0 : 0 < L := by linarith
  have hl := Real.log_pos hL
  have hv : 0 < Real.log L / L := div_pos hl hL0
  have he := Real.add_one_lt_exp hv.ne'
  have hp : L ^ (1 + 1 / L) = L * Real.exp (Real.log L / L) := by
    rw [Real.rpow_def_of_pos hL0, ← Real.exp_log hL0, ← Real.exp_add]
    congr 1
    ring
  dsimp [insertionBarrier]
  rw [hp]
  have hm := mul_lt_mul_of_pos_left he hL0
  have hh : L * (Real.log L / L) = Real.log L := by field_simp
  linarith

private theorem insertion_far_pos {L : ℝ} (hL : 1 < L) :
    0 < insertionBarrier L (Real.exp (L ^ 2)) := by
  have hL0 : 0 < L := by linarith
  have hx : 1 < Real.exp (L ^ 2) := Real.one_lt_exp_iff.mpr (sq_pos_of_pos hL0)
  have hr : 1 + 1 / Real.exp (L ^ 2) < 2 := by
    have hi := (one_div_lt_one₀ (Real.exp_pos _)).mpr hx
    linarith
  have hp := Real.rpow_lt_rpow_of_exponent_lt hL hr
  rw [Real.rpow_two] at hp
  dsimp [insertionBarrier]
  rw [Real.log_exp]
  linarith

private theorem barrier_roots {L z : ℝ} (hL : 16 < L) (hz : 11 < z)
    (hzL : z < L) (hhalf : L - z < 1 / 2)
    (hroot : firstLayerPrice z = 1 / (L * Real.log L)) :
    ∃ α β : ℝ, L / 2 < α ∧ α < z ∧ L < β ∧
      deletionBarrier L α = 0 ∧ insertionBarrier L β = 0 ∧
      (∀ x : ℝ, 1 < x → deletionBarrier L x = 0 → x = α) ∧
      (∀ x : ℝ, 1 < x → insertionBarrier L x = 0 → x = β) := by
  have hL1 : 1 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hhalf1 : 1 < L / 2 := by linarith
  have hhz : L / 2 < z := by linarith
  have ha := deletion_half_pos hL
  have hzneg := deletion_cutoff_neg hL hz hzL hroot
  have hcA : ContinuousOn (deletionBarrier L) (Set.Icc (L / 2) z) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.sub continuousOn_const
      apply (Real.continuous_const_rpow hL0.ne').continuousOn.comp
      · exact continuousOn_id.div (continuousOn_id.add continuousOn_const)
          (fun x hx => by have := hx.1; linarith)
      · exact Set.mapsTo_univ _ _
    · exact continuousOn_id.log (fun x hx => by have := hx.1; linarith)
  obtain ⟨α, hα, hαroot⟩ := intermediate_value_Icc' hhz.le hcA ⟨hzneg.le, ha.le⟩
  have hαlo : L / 2 < α := lt_of_le_of_ne hα.1 (by intro he; rw [← he] at hαroot; linarith)
  have hαhi : α < z := lt_of_le_of_ne hα.2 (by intro he; rw [he] at hαroot; linarith)
  let b := Real.exp (L ^ 2)
  have hLb : L < b := by
    have hl := Real.log_le_sub_one_of_pos hL0
    apply (Real.lt_exp_iff_log_lt hL0).mpr
    dsimp [b]
    nlinarith
  have hbpos := insertion_far_pos hL1
  have hLneg := insertion_at_clock_neg hL1
  have hcB : ContinuousOn (insertionBarrier L) (Set.Icc L b) := by
    apply ContinuousOn.add
    apply ContinuousOn.sub
    · exact continuousOn_id.log (fun x hx => ne_of_gt (hL0.trans_le hx.1))
    · apply (Real.continuous_const_rpow hL0.ne').continuousOn.comp
      · exact continuousOn_const.add (continuousOn_const.div continuousOn_id
          (fun x hx => ne_of_gt (hL0.trans_le hx.1)))
      · exact Set.mapsTo_univ _ _
    · exact continuousOn_const
  obtain ⟨β, hβ, hβroot⟩ := intermediate_value_Icc hLb.le hcB ⟨hLneg.le, hbpos.le⟩
  have hβlo : L < β := lt_of_le_of_ne hβ.1 (by intro he; rw [← he] at hβroot; linarith)
  refine ⟨α, β, hαlo, hαhi, hβlo, hαroot, hβroot, ?_, ?_⟩
  · intro x hx he
    exact (deletion_strictAnti hL1).injOn hx (hhalf1.trans hαlo) (he.trans hαroot.symm)
  · intro x hx he
    exact (insertion_strictMono hL1).injOn hx (hL1.trans hβlo) (he.trans hβroot.symm)

end D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
