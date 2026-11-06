/- GID: D5/S3/Arith/Robin/PriceRecord/ActualBalancedCutoff
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualBalancedCutoff
   mirror-E: none(waiver:real-cutoff-and-exact-support)
   anchors: []
   utility: none
   digest: The same attained Robin minimum has a unique half-shift cutoff and exact prime support. -/

import D5.S3.Arith.Robin.PriceRecord.ActualBalancedExtremizer
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import Mathlib.Topology.Order.IntermediateValue

/-! The real first-layer price extends the existing prime-layer marginal.
The original nonpositive failure supplies its own attained minimum and
unique integer optimizer. No cutoff, root or support is assumed.
This module supplies only cutoff/support, not a signed integral ledger. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff

open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.PaddingRatio
open D5.S3.Arith.Robin.ActualBalancedExtremizer
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

/-- The real extension of the existing first-layer marginal. -/
def firstLayerPrice (t : ℝ) : ℝ := Real.log (1 + 1 / t) / Real.log t

private theorem firstLayerPrice_strictAnti : StrictAntiOn firstLayerPrice (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith only [hx]
  have hy0 : 0 < y := by linarith only [hy]
  have hn : Real.log (1 + 1 / y) < Real.log (1 + 1 / x) :=
    Real.log_lt_log (by positivity) (by linarith only [one_div_lt_one_div_of_lt hx0 hxy])
  have hn0 : 0 < Real.log (1 + 1 / x) := Real.log_pos (by have := one_div_pos.mpr hx0; linarith)
  have hd : Real.log x < Real.log y := Real.log_lt_log hx0 hxy
  exact (div_lt_div_of_pos_right hn (Real.log_pos hy)).trans
    (div_lt_div_of_pos_left hn0 (Real.log_pos hx) hd)

private theorem half_shift_cutoff {L : ℝ} (hL : 12 < L) :
    ∃ z : ℝ, 11 < z ∧ 0 < L - z ∧ L - z < 1 / 2 ∧
      firstLayerPrice z = price L ∧
      (∀ t : ℝ, 1 < t → firstLayerPrice t = price L → t = z) := by
  let a := L - 1 / 2
  have hL0 : 0 < L := by linarith
  have ha : 1 < a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have haL : a < L := by dsimp [a]; linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlow : price L < firstLayerPrice a := by
    have hl := Real.lt_log_one_add_of_pos (one_div_pos.mpr ha0)
    have hid : 2 * (1 / a) / (1 / a + 2) = 1 / L := by
      dsimp [a]
      field_simp
      <;> ring
    rw [hid] at hl
    have hcmp := div_lt_div_of_pos_left (one_div_pos.mpr hL0) hloga
      (Real.log_lt_log ha0 haL)
    change 1 / (L * Real.log L) < Real.log (1 + 1 / a) / Real.log a
    rw [← div_div]
    exact hcmp.trans (div_lt_div_of_pos_right hl hloga)
  have hhigh : firstLayerPrice L < price L := by
    have hl := Real.log_lt_sub_one_of_pos
      (show 0 < 1 + 1 / L by positivity)
      (show 1 + 1 / L ≠ 1 by have := one_div_pos.mpr hL0; linarith)
    have hl' : Real.log (1 + 1 / L) < 1 / L := by linarith only [hl]
    change Real.log (1 + 1 / L) / Real.log L < 1 / (L * Real.log L)
    rw [← div_div]
    exact div_lt_div_of_pos_right hl' hlogL
  have hcont : ContinuousOn firstLayerPrice (Set.Icc a L) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · exact continuousOn_const.add (continuousOn_const.div continuousOn_id
          (fun t ht => ne_of_gt (ha0.trans_le ht.1)))
      · intro t ht
        have ht0 : 0 < t := ha0.trans_le ht.1
        positivity
    · exact continuousOn_id.log (fun t ht => ne_of_gt (ha0.trans_le ht.1))
    · intro t ht
      exact (Real.log_pos (ha.trans_le ht.1)).ne'
  obtain ⟨z, hz, hroot⟩ := intermediate_value_Icc' haL.le hcont ⟨hhigh.le, hlow.le⟩
  have haz : a < z := lt_of_le_of_ne hz.1 (by
    intro heq
    have : firstLayerPrice a = price L := heq.symm ▸ hroot
    linarith only [hlow, this])
  have hzL : z < L := lt_of_le_of_ne hz.2 (by
    intro heq
    have : firstLayerPrice L = price L := heq ▸ hroot
    linarith only [hhigh, this])
  have hz1 : 1 < z := ha.trans haz
  refine ⟨z, ?_, sub_pos.mpr hzL, ?_, hroot, ?_⟩
  · dsimp [a] at haz
    linarith
  · dsimp [a] at haz
    linarith
  · intro t ht heq
    exact firstLayerPrice_strictAnti.injOn ht hz1 (heq.trans hroot.symm)

/-- An original nonpositive Robin failure produces the SAME attained global
minimum and full-domain unique optimizer, together with its unique real
first-layer cutoff in (log N - 1/2, log N) and exact inclusive floor support. -/
theorem failure_has_unique_half_shift_cutoff
    (hfailure : ∃ n : ℕ, 5040 < n ∧ robinLogMargin n ≤ 0) :
    ∃ (N : ℕ) (z : ℝ), 55440 < N ∧ robinLogMargin N ≤ 0 ∧
      (∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m) ∧
      0 < price (Real.log N) ∧ price (Real.log N) < boundaryPrice ∧
      IsGoldenResourceOptimal (price (Real.log N)) N ∧
      (∀ m : ℕ, 1 ≤ m → m ≠ N →
        goldenResourceObjective (price (Real.log N)) m <
          goldenResourceObjective (price (Real.log N)) N) ∧
      N = strictInteger (price (Real.log N)) ∧
      N = maximalInteger (price (Real.log N)) ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        price (Real.log N) ≠ goldenLayerMarginal p k) ∧
      11 < z ∧ 0 < Real.log N - z ∧ Real.log N - z < 1 / 2 ∧
      firstLayerPrice z = 1 / (Real.log N * Real.log (Real.log N)) ∧
      (∀ t : ℝ, 1 < t →
        firstLayerPrice t = 1 / (Real.log N * Real.log (Real.log N)) → t = z) ∧
      N.primeFactors = Nat.primesLE ⌊z⌋₊ := by
  classical
  obtain ⟨N, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie⟩ :=
    failure_has_unique_internal_optimizer hfailure
  have hNlarge : 223092870 ≤ N := by
    by_contra h
    have hf := D5.S3.Arith.Robin.FewDistinctPrimes.robin_lt_223092870
      (by omega : 5040 < N) (by omega : N < 223092870)
    have hnR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hsR : 0 < (ArithmeticFunction.sigma 1 N : ℝ) :=
      Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 N (by omega))
    have hll := loglog_pos (by omega : 5041 ≤ N)
    have hden : 0 < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) :=
      mul_pos (Real.exp_pos _) hll
    have hratio_eq : robinRatio N = ((ArithmeticFunction.sigma 1 N : ℝ) / N) /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N)) := by
      simp only [robinRatio, div_eq_mul_inv, mul_inv_rev]
      ring
    have hratio_lt : robinRatio N < 1 := by
      rw [hratio_eq]
      exact (div_lt_one hden).mpr hf
    have hratio_pos : 0 < robinRatio N :=
      div_pos hsR (mul_pos (mul_pos (Real.exp_pos _) hnR) hll)
    have hmargin : 0 < robinLogMargin N := by
      rw [robin_log_margin_eq_neg_log (by omega : 5041 ≤ N)]
      exact neg_pos.mpr (Real.log_neg hratio_pos hratio_lt)
    linarith only [hSN, hmargin]
  have hL : 12 < Real.log (N : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr (by omega))).mpr
    have hexp : Real.exp (12 : ℝ) = Real.exp 1 ^ 12 := by
      simpa using (Real.exp_nat_mul 1 12)
    rw [hexp]
    have hp : Real.exp 1 ^ 12 < (3 : ℝ) ^ 12 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
    have hn : (223092870 : ℝ) ≤ N := by exact_mod_cast hNlarge
    norm_num at hp
    linarith only [hp, hn]
  obtain ⟨z, hz, hM0, hMhalf, hroot, hunique⟩ := half_shift_cutoff hL
  have hsupport : N.primeFactors = Nat.primesLE ⌊z⌋₊ := by
    ext p
    by_cases hp : p.Prime
    · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hz1 : 1 < z := by linarith
      have hcompare : price (Real.log N) ≤ goldenLayerMarginal p 1 ↔ (p : ℝ) ≤ z := by
        rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
        change price (Real.log N) ≤ firstLayerPrice p ↔ (p : ℝ) ≤ z
        rw [← hroot]
        constructor
        · intro h
          by_contra hn
          exact (not_lt_of_ge h) (firstLayerPrice_strictAnti hz1 hp1 (lt_of_not_ge hn))
        · intro h
          exact firstLayerPrice_strictAnti.antitoneOn hp1 hz1 h
      have hlayer := weak_layer_iff hp0 hp (show 1 ≤ (1 : ℕ) by omega)
      rw [← hNm, hcompare] at hlayer
      have hfactor : p ∈ N.primeFactors ↔ 1 ≤ N.factorization p := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        omega
      rw [hfactor, hlayer, Nat.mem_primesLE, and_iff_right hp]
      exact (Nat.le_floor_iff (by linarith : 0 ≤ z)).symm
    · simp [Nat.mem_primeFactors, Nat.mem_primesLE, hp]
  exact ⟨N, z, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie,
    hz, hM0, hMhalf, hroot, hunique, hsupport⟩

#print axioms failure_has_unique_half_shift_cutoff
end D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
