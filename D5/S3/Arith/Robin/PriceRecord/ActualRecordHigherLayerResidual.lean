/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Complete actual higher-layer loss vanishes at the critical scale uniformly in literal record prices. -/

import D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import D5.S3.Arith.Robin.ActualGlobalBracketing
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The finite support below comes from the canonical unrestricted strict integer,
without an extra restriction on the given integer or its prime exponents.
The uniform residual uses fixed real endpoint tails and the original integer
logarithmic clock, with a threshold uniform in the original record price. -/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual

open Finset Real Filter
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.EulerLayerRootCorrection (strict_inventory_third_layer_mass)
open D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer (price_record_missing_layer)
open D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder (record_third_mass_bound record_mass_limits record_log_envelope record_layer_ratio
    record_second_own_clock_limit)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (theta_error_log_power)

private theorem reference_price_pos {X : ℝ} (hX : 1 < X) :
    0 < referencePrice X :=
  one_div_pos.mpr (mul_pos (by linarith) (log_pos hX))

local notation "pressureOptimizer" =>
  D5.S3.Arith.Robin.ActualTwoPriceDefect.strictInteger ∘ referencePrice

private theorem pressure_optimizer_spec {X : ℝ} (hX : 1 < X) :
    1 ≤ pressureOptimizer X ∧
    (∀ p : ℕ, (pressureOptimizer X).factorization p =
      optimalLayerCount (referencePrice X) p) ∧
    IsGoldenResourceOptimal (referencePrice X) (pressureOptimizer X) := by
  exact ⟨D5.S3.Arith.Robin.ActualTwoPriceDefect.strictInteger_pos (reference_price_pos hX),
    D5.S3.Arith.Robin.ActualTwoPriceDefect.strictInteger_counts (reference_price_pos hX),
    D5.S3.Arith.Robin.ActualGlobalBracketing.strict_is_optimal (reference_price_pos hX)⟩

/-- All active optimizer primes AND all primes occupied by the original integer. -/
def lossPrimes (X : ℝ) (n : ℕ) : Finset ℕ :=
  (pressureOptimizer X).primeFactors ∪ n.primeFactors

/-- This is the raw objective increment, not the marginal divided by log(p). -/
def rawLayerMargin (X : ℝ) (p j : ℕ) : ℝ :=
  log p * (goldenLayerMarginal p j - referencePrice X)

/-- Complete loss at one actual prime-layer coordinate. -/
def layerLoss (X : ℝ) (n p j : ℕ) : ℝ :=
  max (rawLayerMargin X p j) 0 -
    if j ≤ n.factorization p then rawLayerMargin X p j else 0

def layerCutoff (X : ℝ) (n p : ℕ) : ℕ :=
  max (optimalLayerCount (referencePrice X) p) (n.factorization p)

/-- Includes absent positive-gain primes and occupied negative-gain primes. -/
def completeFirstLayerLoss (X : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ lossPrimes X n, layerLoss X n p 1

def completeSecondLayerLoss (X : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ lossPrimes X n, layerLoss X n p 2

/-- Every higher coordinate up to either the actual or the optimizer exponent. -/
def completeHigherLayerLoss (X : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ lossPrimes X n, ∑ j ∈ Icc 3 (layerCutoff X n p), layerLoss X n p j

theorem layer_loss_nonneg (X : ℝ) (n p j : ℕ) :
    0 ≤ layerLoss X n p j := by
  unfold layerLoss
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · simpa using le_max_right (rawLayerMargin X p j) 0

theorem margin_active_iff {X : ℝ} (hX : 1 < X) {p j : ℕ}
    (hp : p.Prime) (hj : 1 ≤ j) :
    0 < rawLayerMargin X p j ↔ j ≤ optimalLayerCount (referencePrice X) p := by
  have hi := Set.ext_iff.mp
    (positive_layers_eq_count_interval (reference_price_pos hX) hp) j
  simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hi
  have hg : 0 < rawLayerMargin X p j ↔ referencePrice X < goldenLayerMarginal p j := by
    unfold rawLayerMargin
    exact (mul_pos_iff_of_pos_left hp.log_pos).trans sub_pos
  rw [hg]
  tauto

private theorem loss_above_cutoff {X : ℝ} (hX : 1 < X) (n : ℕ) {p j : ℕ}
    (hp : p.Prime) (hj : 1 ≤ j) (hc : layerCutoff X n p < j) :
    layerLoss X n p j = 0 := by
  have ha : ¬ j ≤ n.factorization p := by dsimp [layerCutoff] at hc; omega
  have hg : rawLayerMargin X p j ≤ 0 := by
    apply le_of_not_gt
    intro hg
    have := (margin_active_iff hX hp hj).mp hg
    dsimp [layerCutoff] at hc
    omega
  simp [layerLoss, ha, max_eq_right hg]

private theorem local_complete_loss {X : ℝ} (hX : 1 < X) (n : ℕ) {p : ℕ}
    (hp : p.Prime) :
    (∑ j ∈ Icc 1 (layerCutoff X n p), layerLoss X n p j) =
      goldenPrimeLocalObjective (referencePrice X) p
        (optimalLayerCount (referencePrice X) p) -
      goldenPrimeLocalObjective (referencePrice X) p (n.factorization p) := by
  classical
  let c := optimalLayerCount (referencePrice X) p
  let a := n.factorization p
  let M := layerCutoff X n p
  have hcM : c ≤ M := le_max_left _ _
  have haM : a ≤ M := le_max_right _ _
  have hpositive : (∑ j ∈ Icc 1 M, max (rawLayerMargin X p j) 0) =
      ∑ j ∈ Icc 1 c, rawLayerMargin X p j := by
    calc
      _ = ∑ j ∈ Icc 1 M, if j ≤ c then rawLayerMargin X p j else 0 := by
        apply sum_congr rfl
        intro j hj
        have hh := margin_active_iff hX hp (mem_Icc.mp hj).1
        by_cases hjc : j ≤ c
        · rw [ite_eq_left hjc, max_eq_left (hh.mpr hjc).le]
        · rw [ite_eq_right hjc, max_eq_right (le_of_not_gt (fun h => hjc (hh.mp h)))]
      _ = ∑ j ∈ (Icc 1 M).filter (fun j => j ≤ c), rawLayerMargin X p j :=
        (sum_filter _ _).symm
      _ = _ := by
        congr 1
        ext j
        simp only [mem_filter, mem_Icc]
        omega
  have hoccupied : (∑ j ∈ Icc 1 M,
      if j ≤ a then rawLayerMargin X p j else 0) =
      ∑ j ∈ Icc 1 a, rawLayerMargin X p j := by
    rw [← sum_filter]
    congr 1
    ext j
    simp only [mem_filter, mem_Icc]
    omega
  change (∑ j ∈ Icc 1 M, (max (rawLayerMargin X p j) 0 -
    (if j ≤ a then rawLayerMargin X p j else 0))) = _
  rw [sum_sub_distrib, hpositive, hoccupied]
  rw [local_eq_layer_sum (referencePrice X) hp,
    local_eq_layer_sum (referencePrice X) hp]
  rfl

private theorem local_split_first_two {X : ℝ} (hX : 1 < X) (n : ℕ) {p : ℕ}
    (hp : p.Prime) :
    (∑ j ∈ Icc 1 (layerCutoff X n p), layerLoss X n p j) =
      layerLoss X n p 1 + layerLoss X n p 2 +
        ∑ j ∈ Icc 3 (layerCutoff X n p), layerLoss X n p j := by
  classical
  let M := layerCutoff X n p
  rcases (show M = 0 ∨ M = 1 ∨ 2 ≤ M by omega) with hm | hm | hm
  · have h1 := loss_above_cutoff hX n hp (by norm_num : 1 ≤ (1 : ℕ)) (by omega : M < 1)
    have h2 := loss_above_cutoff hX n hp (by norm_num : 1 ≤ (2 : ℕ)) (by omega : M < 2)
    change (∑ j ∈ Icc 1 M, layerLoss X n p j) =
      layerLoss X n p 1 + layerLoss X n p 2 + ∑ j ∈ Icc 3 M, layerLoss X n p j
    simp [hm, h1, h2]
  · have h2 := loss_above_cutoff hX n hp (by norm_num : 1 ≤ (2 : ℕ)) (by omega : M < 2)
    change (∑ j ∈ Icc 1 M, layerLoss X n p j) =
      layerLoss X n p 1 + layerLoss X n p 2 + ∑ j ∈ Icc 3 M, layerLoss X n p j
    simp [hm, h2]
  · have hs : Icc 1 M = insert 1 (insert 2 (Icc 3 M)) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    change (∑ j ∈ Icc 1 M, layerLoss X n p j) =
      layerLoss X n p 1 + layerLoss X n p 2 + ∑ j ∈ Icc 3 M, layerLoss X n p j
    rw [hs, sum_insert (by simp), sum_insert (by simp)]
    ring

theorem actual_defect_decomposition {X : ℝ} (hX : 1 < X) {n : ℕ}
    (hn : 1 ≤ n) :
    actualDefect X n = completeFirstLayerLoss X n + completeSecondLayerLoss X n +
      completeHigherLayerLoss X n := by
  classical
  obtain ⟨hU, hc, hopt⟩ := pressure_optimizer_spec hX
  let S := lossPrimes X n
  have hUS : (pressureOptimizer X).primeFactors ⊆ S := subset_union_left
  have hnS : n.primeFactors ⊆ S := subset_union_right
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hpressure : actualPressure X =
      goldenResourceObjective (referencePrice X) (pressureOptimizer X) := by
    unfold actualPressure
    rw [golden_resource_supremum_eq_positive_part_sum (reference_price_pos hX),
      ← objective_at_optimal_eq_positive_part_sum (reference_price_pos hX) hU hc]
  unfold actualDefect
  rw [hpressure, golden_resource_objective_sum_on _ hU S hUS,
    golden_resource_objective_sum_on _ hn S hnS, ← sum_sub_distrib]
  change (∑ p ∈ S, _) =
    (∑ p ∈ S, layerLoss X n p 1) + (∑ p ∈ S, layerLoss X n p 2) +
      ∑ p ∈ S, ∑ j ∈ Icc 3 (layerCutoff X n p), layerLoss X n p j
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [hc p, ← local_complete_loss hX n (hprime p hp),
    local_split_first_two hX n (hprime p hp)]

private theorem raw_gain_nonneg {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    0 ≤ log p * goldenLayerMarginal p j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have hg := golden_layer_gain_lower hp hj
  have hb : 0 ≤ (1 - (p : ℝ)⁻¹) * (p : ℝ)⁻¹ ^ j :=
    mul_nonneg (sub_pos.mpr hi).le (pow_nonneg (inv_nonneg.mpr hp0.le) j)
  simpa only [mul_comm] using hb.trans hg

/-- Finite telescoping into the original Euler truncation. The record tail bound
itself is NOT reproved here: its consumer below calls price_record_missing_layer. -/
private theorem finite_raw_tail {p : ℕ} (hp : p.Prime) (a c : ℕ) :
    (∑ j ∈ Icc (a + 1) c, log p * goldenLayerMarginal p j) ≤
      -log (1 - (p : ℝ)⁻¹ ^ (a + 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi0 : 0 ≤ (p : ℝ)⁻¹ := (inv_pos.mpr hp0).le
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have ha0 : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ hi0 hi (by omega))
  have hca0 : 0 < 1 - (p : ℝ)⁻¹ ^ (c + 1) :=
    sub_pos.mpr (pow_lt_one₀ hi0 hi (by omega))
  have htail0 : 0 ≤ -log (1 - (p : ℝ)⁻¹ ^ (a + 1)) := by
    have hl := log_le_log ha0 (sub_le_self _ (pow_nonneg hi0 _))
    rw [log_one] at hl
    exact neg_nonneg.mpr hl
  by_cases hac : a ≤ c
  · have hs : Icc 1 c = Icc 1 a ∪ Icc (a + 1) c := by
      ext j
      simp only [mem_Icc, mem_union]
      omega
    have hd : Disjoint (Icc 1 a) (Icc (a + 1) c) := by
      apply disjoint_left.mpr
      intro j hj hja
      simp only [mem_Icc] at hj hja
      omega
    have hc := local_eq_layer_sum (0 : ℝ) hp c
    have ha := local_eq_layer_sum (0 : ℝ) hp a
    simp only [sub_zero] at hc ha
    rw [hs, sum_union hd] at hc
    have heq : (∑ j ∈ Icc (a + 1) c, log p * goldenLayerMarginal p j) =
        goldenPrimeLocalObjective 0 p c - goldenPrimeLocalObjective 0 p a := by linarith
    rw [heq, goldenPrimeLocalObjective, goldenPrimeLocalObjective]
    simp only [zero_mul, sub_zero]
    rw [log_div hca0.ne' (sub_pos.mpr hi).ne', log_div ha0.ne' (sub_pos.mpr hi).ne']
    have hl := log_le_log hca0 (sub_le_self _ (pow_nonneg hi0 _))
    rw [log_one] at hl
    linarith
  · have hs : Icc (a + 1) c = ∅ := by apply Icc_eq_empty; omega
    simpa only [hs, sum_empty] using htail0

private def missingHigherAt (X : ℝ) (n p : ℕ) : ℝ :=
  ∑ j ∈ Icc 3 (layerCutoff X n p),
    if n.factorization p < j then max (rawLayerMargin X p j) 0 else 0

private def occupiedHigherAt (X : ℝ) (n p : ℕ) : ℝ :=
  ∑ j ∈ Icc 3 (layerCutoff X n p),
    if j ≤ n.factorization p then max (-rawLayerMargin X p j) 0 else 0

private theorem higher_at_split (X : ℝ) (n p : ℕ) :
    (∑ j ∈ Icc 3 (layerCutoff X n p), layerLoss X n p j) =
      missingHigherAt X n p + occupiedHigherAt X n p := by
  unfold missingHigherAt occupiedHigherAt
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  unfold layerLoss
  by_cases hj : j ≤ n.factorization p
  · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_right (not_lt.mpr hj), zero_add]
    by_cases hg : 0 ≤ rawLayerMargin X p j
    · simp [max_eq_left hg, max_eq_right (neg_nonpos.mpr hg)]
    · have hg' : rawLayerMargin X p j ≤ 0 := le_of_not_ge hg
      simp [max_eq_right hg', max_eq_left (neg_nonneg.mpr hg')]
  · simp [hj, Nat.lt_of_not_ge hj]

private theorem missing_higher_le_raw_tail {X : ℝ} (hX : 1 < X) (n : ℕ)
    {p : ℕ} (hp : p.Prime) :
    missingHigherAt X n p ≤ -log (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1)) := by
  classical
  let a := n.factorization p
  let c := optimalLayerCount (referencePrice X) p
  let T := (Icc 3 (layerCutoff X n p)).filter (fun j => a < j ∧ j ≤ c)
  have heq : missingHigherAt X n p = ∑ j ∈ T, rawLayerMargin X p j := by
    unfold missingHigherAt T
    rw [sum_filter]
    apply sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := by have := (mem_Icc.mp hj).1; omega
    have hh := margin_active_iff hX hp hj1
    by_cases haj : a < j
    · by_cases hjc : j ≤ c
      · simp only [show n.factorization p = a from rfl, haj, hjc, and_self,
          ite_eq_left, max_eq_left (hh.mpr hjc).le]
      · have hn : rawLayerMargin X p j ≤ 0 := le_of_not_gt (fun h => hjc (hh.mp h))
        simp [show n.factorization p = a from rfl, haj, hjc, max_eq_right hn]
    · simp [show n.factorization p = a from rfl, haj]
  have hsub : T ⊆ Icc (a + 1) c := by
    intro j hj
    have := (mem_filter.mp hj).2
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  calc
    _ = ∑ j ∈ T, rawLayerMargin X p j := heq
    _ ≤ ∑ j ∈ T, log p * goldenLayerMarginal p j := by
      apply sum_le_sum
      intro j _
      unfold rawLayerMargin
      nlinarith [mul_nonneg (reference_price_pos hX).le hp.log_pos.le]
    _ ≤ ∑ j ∈ Icc (a + 1) c, log p * goldenLayerMarginal p j :=
      sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ =>
        raw_gain_nonneg hp (by have := (mem_Icc.mp hj).1; omega))
    _ ≤ _ := finite_raw_tail hp a c

private theorem occupied_higher_bound {X : ℝ} (hX : 1 < X) (n : ℕ) {p : ℕ}
    (hp : p.Prime) :
    occupiedHigherAt X n p ≤ referencePrice X *
      ((n.factorization p - 2 : ℕ) : ℝ) * log p := by
  classical
  have hlambda : 0 < referencePrice X := reference_price_pos hX
  let a := n.factorization p
  have heq : (Icc 3 (layerCutoff X n p)).filter (fun j => j ≤ a) = Icc 3 a := by
    ext j
    simp only [mem_filter, mem_Icc, layerCutoff]
    omega
  unfold occupiedHigherAt
  rw [← sum_filter, heq]
  calc
    _ ≤ ∑ _j ∈ Icc 3 a, referencePrice X * log p := by
      apply sum_le_sum
      intro j hj
      apply max_le _ (by positivity)
      have hg := raw_gain_nonneg (j := j) hp (by have := (mem_Icc.mp hj).1; omega)
      unfold rawLayerMargin
      nlinarith
    _ = _ := by
      have hc : (Icc 3 a).card = a - 2 := by rw [Nat.card_Icc]; omega
      simp only [sum_const, hc, nsmul_eq_mul]
      dsimp [a]
      ring

private theorem positive_higher_prime_lt {X R : ℝ} (hX : 1 < X) (hR : 1 ≤ R)
    (hclock : X * log X ≤ log 2 * R ^ 3) {p j : ℕ}
    (hp : p.Prime) (hj : 3 ≤ j) (hg : 0 < rawLayerMargin X p j) : (p : ℝ) < R := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hi0 : 0 ≤ (p : ℝ)⁻¹ := (inv_pos.mpr hp0).le
  have hi : (p : ℝ)⁻¹ ≤ 1 :=
    ((inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)).le
  have hpow : (p : ℝ)⁻¹ ^ j ≤ (p : ℝ)⁻¹ ^ 3 := pow_le_pow_of_le_one hi0 hi hj
  have hb := (le_div_iff₀ hp.log_pos).mp
    (golden_layer_marginal_le_inv_pow hp (by omega : 1 ≤ j))
  have hprice : referencePrice X * log p < log p * goldenLayerMarginal p j := by
    unfold rawLayerMargin at hg
    nlinarith
  have hlog2 : log (2 : ℝ) ≤ log p := log_le_log (by norm_num) hp2
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos hX
  have hstep : log 2 / (X * log X) < 1 / (p : ℝ) ^ 3 := by
    calc
      _ ≤ referencePrice X * log p := by
        simpa only [referencePrice, div_eq_mul_inv, one_mul, mul_comm] using
          div_le_div_of_nonneg_right hlog2 (mul_pos hX0 hL).le
      _ < log p * goldenLayerMarginal p j := hprice
      _ ≤ (p : ℝ)⁻¹ ^ j := by simpa [mul_comm] using hb
      _ ≤ (p : ℝ)⁻¹ ^ 3 := hpow
      _ = _ := by simp [inv_pow, one_div]
  have hc := (div_lt_div_iff₀ (mul_pos hX0 hL) (pow_pos hp0 3)).mp hstep
  by_contra! hRp
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ R) hRp 3
  have hmul := mul_le_mul_of_nonneg_left hp3 (log_pos (by norm_num : (1 : ℝ) < 2)).le
  nlinarith

/-- The entire missing higher Euler tail is charged once per prime, not once
per layer. No assumption on v_P(m), no exponent cap and no exchange reproof.
R is a deterministic clock parameter satisfying XL <= log(2) R^3, not an
assumed restriction on the support of the original integer. -/
theorem finite_complete_higher_layer_bound {X R : ℝ} {m : ℕ} {mu : ℝ}
    (hX : 1 < X) (hm : 2 ≤ m) (hmu : 0 < mu)
    (hrecord : ∀ k : ℕ, 0 < k → k < m →
      goldenResourceObjective mu k < goldenResourceObjective mu m)
    (hR : 1 ≤ R) (hRP : R < (largestPrime m : ℝ))
    (hclock : X * log X ≤ log 2 * R ^ 3) :
    0 ≤ completeHigherLayerLoss X m ∧
    completeHigherLayerLoss X m ≤
      2 * (⌊R⌋₊ : ℝ) / (largestPrime m : ℝ) +
        referencePrice X * strict_inventory_third_layer_mass m ∧
    completeHigherLayerLoss X m ≤
      2 * R / (largestPrime m : ℝ) + referencePrice X *
        ((layerPrime m 3 : ℝ) * log (4 * (largestPrime m : ℝ) ^ 2)) := by
  classical
  let P := largestPrime m
  let S := lossPrimes X m
  let V := S.filter (fun p : ℕ => (p : ℝ) ≤ R)
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hP2 : 2 ≤ P := hq.two_le.trans
    (le_sup (f := id) (hq.mem_primeFactors hqm (by omega : m ≠ 0)))
  have hPmem : P ∈ m.primeFactors := by
    obtain ⟨p, hp, he⟩ := exists_mem_eq_sup m.primeFactors
      ⟨q, hq.mem_primeFactors hqm (by omega : m ≠ 0)⟩ id
    change P = p at he
    simpa only [he] using hp
  have hP : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hPm : P ∣ m := Nat.dvd_of_mem_primeFactors hPmem
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hout (p : ℕ) (hp : p ∈ S) (hpV : p ∉ V) : missingHigherAt X m p = 0 := by
    have hRp : R < (p : ℝ) := by
      by_contra! h
      exact hpV (mem_filter.mpr ⟨hp, h⟩)
    unfold missingHigherAt
    apply sum_eq_zero
    intro j hj
    split_ifs
    · apply max_eq_right
      apply le_of_not_gt
      intro hg
      exact (not_lt_of_ge hRp.le) (positive_higher_prime_lt hX hR hclock (hprime p hp)
        (mem_Icc.mp hj).1 hg)
    · rfl
  have hmiss (p : ℕ) (hpV : p ∈ V) : missingHigherAt X m p ≤ 2 / (P : ℝ) := by
    obtain ⟨hpS, hpR⟩ := mem_filter.mp hpV
    have hpp := hprime p hpS
    have hpP : p < P := by exact_mod_cast hpR.trans_lt hRP
    have ht := price_record_missing_layer (by omega : 0 < m) hmu hrecord hP hPm hpp hpP
    dsimp only at ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, htail⟩ := ht
    exact (missing_higher_le_raw_tail hX m hpp).trans htail.le
  have hcard : (V.card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by
    have hsub : V ⊆ Ioc 0 ⌊R⌋₊ := by
      intro p hp
      obtain ⟨hpS, hpR⟩ := mem_filter.mp hp
      exact mem_Ioc.mpr ⟨(hprime p hpS).pos, Nat.le_floor hpR⟩
    have hc := card_le_card hsub
    exact_mod_cast (by simpa using hc : V.card ≤ ⌊R⌋₊)
  have hmissing : (∑ p ∈ S, missingHigherAt X m p) ≤ 2 * (⌊R⌋₊ : ℝ) / (P : ℝ) := by
    calc
      _ = ∑ p ∈ V, missingHigherAt X m p := by
        symm
        apply sum_subset (filter_subset _ _)
        intro p hp hpV
        exact hout p hp hpV
      _ ≤ ∑ _p ∈ V, 2 / (P : ℝ) := sum_le_sum hmiss
      _ = (V.card : ℝ) * (2 / (P : ℝ)) := by simp
      _ ≤ (⌊R⌋₊ : ℝ) * (2 / (P : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hmass : (∑ p ∈ S, ((m.factorization p - 2 : ℕ) : ℝ) * log p) =
      strict_inventory_third_layer_mass m := by
    have hsub : m.primeFactors ⊆ S := subset_union_right
    have hsum : (∑ p ∈ S, ((m.factorization p - 2 : ℕ) : ℝ) * log p) =
        ∑ p ∈ m.primeFactors, ((m.factorization p - 2 : ℕ) : ℝ) * log p := by
      symm
      apply sum_subset hsub
      intro p _ hp
      have hv : m.factorization p = 0 := by
        simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
      simp [hv]
    rw [hsum, strict_inventory_third_layer_mass, sum_filter]
    apply sum_congr rfl
    intro p _
    split_ifs with h
    · rfl
    · have hv : m.factorization p - 2 = 0 := by omega
      simp [hv]
  have hoccupied : (∑ p ∈ S, occupiedHigherAt X m p) ≤
      referencePrice X * strict_inventory_third_layer_mass m := by
    calc
      _ ≤ ∑ p ∈ S, referencePrice X * ((m.factorization p - 2 : ℕ) : ℝ) * log p :=
        sum_le_sum (fun p hp => occupied_higher_bound hX m (hprime p hp))
      _ = referencePrice X * strict_inventory_third_layer_mass m := by
        rw [← hmass, mul_sum]
        apply sum_congr rfl
        intro p _
        ring
  have hsplit : completeHigherLayerLoss X m =
      (∑ p ∈ S, missingHigherAt X m p) + ∑ p ∈ S, occupiedHigherAt X m p := by
    unfold completeHigherLayerLoss
    change (∑ p ∈ S, _) = _
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun p _ => higher_at_split X m p)
  have hfin : completeHigherLayerLoss X m ≤
      2 * (⌊R⌋₊ : ℝ) / (P : ℝ) + referencePrice X * strict_inventory_third_layer_mass m := by
    rw [hsplit]
    exact add_le_add hmissing hoccupied
  have hthird := record_third_mass_bound hm hmu hrecord
  refine ⟨sum_nonneg (fun p _ => sum_nonneg (fun j _ => layer_loss_nonneg X m p j)), hfin, ?_⟩
  calc
    _ ≤ 2 * (⌊R⌋₊ : ℝ) / (P : ℝ) + referencePrice X * strict_inventory_third_layer_mass m := hfin
    _ ≤ 2 * R / (P : ℝ) + referencePrice X *
        ((layerPrime m 3 : ℝ) * log (4 * (P : ℝ) ^ 2)) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0 ≤ R)) (by norm_num)) hP0.le
      · exact mul_le_mul_of_nonneg_left hthird.2 (reference_price_pos hX).le

/-- The real extension of the EXACT second raw margin. -/
def secondRawMargin (X t : ℝ) : ℝ :=
  log ((1 - t⁻¹ ^ 3) / (1 - t⁻¹ ^ 2)) - log t / (X * log X)

def secondTubePoint (X s : ℝ) : ℝ := sqrt X * (sqrt 2 + s / log X)

def secondTubeCenter : ℝ := -log 2 / sqrt 2

def secondExpansionError (X K : ℝ) : ℝ :=
  (4 * K ^ 2 + 2 * K / sqrt 2) / log X +
    12 * log X / ((sqrt 2) ^ 3 * sqrt X)

private theorem second_margin_at_prime (X : ℝ) {p : ℕ} (hp : p.Prime) :
    rawLayerMargin X p 2 = secondRawMargin X p := by
  unfold rawLayerMargin goldenLayerMarginal secondRawMargin referencePrice
  norm_num only
  field_simp [hp.log_pos.ne'] <;> ring

private theorem real_second_gain_error {t : ℝ} (ht : 1 < t) :
    |log ((1 - t⁻¹ ^ 3) / (1 - t⁻¹ ^ 2)) - 1 / t ^ 2| ≤ 3 / (2 * t ^ 3) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  have hi : t⁻¹ < 1 := (inv_lt_one₀ ht0).mpr ht
  have hd : 1 - t⁻¹ ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ (inv_nonneg.mpr ht0.le) hi (by norm_num))).ne'
  have hr : (1 - t⁻¹ ^ 3) / (1 - t⁻¹ ^ 2) = 1 + 1 / (t * (t + 1)) := by
    apply (div_eq_iff hd).mpr
    field_simp [ht0.ne', ht1.ne'] <;> ring
  rw [hr]
  let q := 1 / (t * (t + 1))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : log (1 + q) ≤ q := by
    have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + q)
    linarith
  have hl : q - q ^ 2 / 2 ≤ log (1 + q) := by
    have h := le_log_one_add_of_nonneg hq
    have hb : q - q ^ 2 / 2 ≤ 2 * q / (q + 2) := by
      apply (le_div_iff₀ (by positivity : 0 < q + 2)).mpr
      nlinarith [pow_nonneg hq 3]
    exact hb.trans h
  have hq2 : q ≤ 1 / t ^ 2 := by
    dsimp [q]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hdiff : 1 / t ^ 2 - q = 1 / (t ^ 2 * (t + 1)) := by
    dsimp [q]
    field_simp [ht0.ne', ht1.ne'] <;> ring
  have hdiffle : 1 / t ^ 2 - q ≤ 1 / t ^ 3 := by
    rw [hdiff]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg t]
  have hqSq : q ^ 2 ≤ 1 / t ^ 4 := by
    calc
      q ^ 2 ≤ (1 / t ^ 2) ^ 2 := pow_le_pow_left₀ hq hq2 2
      _ = _ := by field_simp [ht0.ne'] <;> ring
  have hfour : 1 / t ^ 4 ≤ 1 / t ^ 3 := by
    apply one_div_le_one_div_of_le (by positivity)
    calc
      t ^ 3 = 1 * t ^ 3 := by ring
      _ ≤ t * t ^ 3 := mul_le_mul_of_nonneg_right ht.le (pow_nonneg ht0.le 3)
      _ = t ^ 4 := by ring
  change |log (1 + q) - 1 / t ^ 2| ≤ _
  rw [abs_of_nonpos (by linarith : log (1 + q) - 1 / t ^ 2 ≤ 0)]
  have heq : 1 / t ^ 3 + 1 / t ^ 3 / 2 = 3 / (2 * t ^ 3) := by ring
  rw [← heq]
  linarith

private theorem log_near_sqrt_two {h : ℝ} (hh : |h| ≤ sqrt 2 / 2) :
    |log (sqrt 2 + h) - log (sqrt 2)| ≤ 2 * |h| / sqrt 2 := by
  let a := sqrt (2 : ℝ)
  have ha : 0 < a := sqrt_pos.mpr (by norm_num)
  have hab := by simpa only [neg_div] using abs_le.mp hh
  have hu : 0 < a + h := by linarith [hab.1]
  have hr : 0 < (a + h) / a := div_pos hu ha
  have hlog : log ((a + h) / a) = log (a + h) - log a := log_div hu.ne' ha.ne'
  have hupper := log_le_sub_one_of_pos hr
  have hlower := one_sub_inv_le_log_of_pos hr
  rw [hlog] at hupper hlower
  have he1 : (a + h) / a - 1 = h / a := by field_simp [ha.ne']; ring
  have he2 : 1 - ((a + h) / a)⁻¹ = h / (a + h) := by
    field_simp [ha.ne', hu.ne']; ring
  rw [he1] at hupper
  rw [he2] at hlower
  change |log (a + h) - log a| ≤ 2 * |h| / a
  apply abs_le.mpr
  constructor
  · have hb : -(2 * |h| / a) ≤ h / (a + h) := by
      rw [← neg_div]
      apply (div_le_div_iff₀ ha hu).mpr
      have hprod := mul_nonneg (abs_nonneg h) (by linarith [hab.1] : 0 ≤ a + 2 * h)
      nlinarith [mul_le_mul_of_nonneg_right (neg_abs_le h) ha.le]
    exact hb.trans hlower
  · exact hupper.trans ((div_le_div_iff_of_pos_right ha).mpr
      (by linarith [le_abs_self h, abs_nonneg h]))

private theorem inverse_square_remainder {h : ℝ} (hh : |h| ≤ sqrt 2 / 2) :
    |1 / (sqrt 2 + h) ^ 2 - 1 / 2 + h / sqrt 2| ≤ 4 * h ^ 2 := by
  let a := sqrt (2 : ℝ)
  have ha : 0 < a := sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 2 := sq_sqrt (by norm_num)
  have ha3 : a ^ 3 = 2 * a := by nlinarith [congrArg (fun x : ℝ => a * x) ha2]
  have hh' : -a / 2 ≤ h ∧ h ≤ a / 2 := by simpa only [neg_div] using abs_le.mp hh
  have hu : 0 < a + h := by linarith [hh'.1]
  have hu2 : 1 / 2 ≤ (a + h) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a / 2)
      (by linarith [hh'.1] : a / 2 ≤ a + h) 2
    nlinarith
  have hd : 0 < 2 * a * (a + h) ^ 2 := by positivity
  have hnum : 0 ≤ 3 * a + 2 * h := by linarith [hh'.1]
  have hid : 1 / (a + h) ^ 2 - 1 / 2 + h / a =
      h ^ 2 * (3 * a + 2 * h) / (2 * a * (a + h) ^ 2) := by
    field_simp [ha.ne', hu.ne']
    nlinarith [ha3]
  change |1 / (a + h) ^ 2 - 1 / 2 + h / a| ≤ _
  rw [hid, abs_of_nonneg (by positivity :
    0 ≤ h ^ 2 * (3 * a + 2 * h) / (2 * a * (a + h) ^ 2))]
  apply (div_le_iff₀ hd).mpr
  have hn := mul_le_mul_of_nonneg_left (by linarith [hh'.2] : 3 * a + 2 * h ≤ 4 * a)
    (sq_nonneg h)
  have hden := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 2 * a)
  have hp := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 4 * h ^ 2)
  nlinarith

/-- A quantitative compact-uniform expansion of the raw second-layer margin.
K is fixed before X and s. No shrinking-window uniformity is assumed. -/
theorem compact_second_raw_margin {X K s : ℝ} (hX : 1 < X) (hK : 0 ≤ K)
    (hs : |s| ≤ K) (hlarge : 2 * K ≤ sqrt 2 * log X)
    (ht : 1 < secondTubePoint X s) :
    |X * log X * secondRawMargin X (secondTubePoint X s) +
      s / sqrt 2 + log (sqrt 2)| ≤ secondExpansionError X K := by
  let a := sqrt (2 : ℝ)
  let L := log X
  let r := sqrt X
  let h := s / L
  let u := a + h
  let t := r * u
  have ha : 0 < a := sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 2 := sq_sqrt (by norm_num)
  have hL : 0 < L := log_pos hX
  have hX0 : 0 < X := by linarith
  have hr : 0 < r := sqrt_pos.mpr hX0
  have hr2 : r ^ 2 = X := sq_sqrt hX0.le
  have hh : |h| ≤ a / 2 := by
    rw [show |h| = |s| / L by simp [h, abs_div, abs_of_pos hL]]
    apply (div_le_iff₀ hL).mpr
    nlinarith
  have hu : 0 < u := by
    have := (abs_le.mp hh).1
    dsimp [u]
    linarith
  have hutwo : a / 2 ≤ u := by
    dsimp [u]
    linarith [(abs_le.mp hh).1]
  have ht' : 1 < t := ht
  have he := real_second_gain_error ht'
  have hinv := inverse_square_remainder hh
  have hlog := log_near_sqrt_two hh
  have hs2 : s ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hK).mpr hs
  have hlogbound : |log u - log a| ≤ (2 * K / a) / L := by
    calc
      _ ≤ 2 * |h| / a := hlog
      _ = (2 * |s| / a) / L := by
        simp only [h, abs_div, abs_of_pos hL]
        ring
      _ ≤ _ := by gcongr
  have hinvbound : |L * (1 / u ^ 2 - 1 / 2) + s / a| ≤ 4 * K ^ 2 / L := by
    have heq : L * (1 / u ^ 2 - 1 / 2) + s / a =
        L * (1 / u ^ 2 - 1 / 2 + h / a) := by
      dsimp [h]
      field_simp [hL.ne'] <;> ring
    rw [heq, abs_mul, abs_of_pos hL]
    calc
      _ ≤ L * (4 * h ^ 2) := mul_le_mul_of_nonneg_left hinv hL.le
      _ = 4 * s ^ 2 / L := by dsimp [h]; field_simp [hL.ne'] <;> ring
      _ ≤ _ := by gcongr
  have hgainbound : |X * L *
      (log ((1 - t⁻¹ ^ 3) / (1 - t⁻¹ ^ 2)) - 1 / t ^ 2)| ≤
      12 * L / (a ^ 3 * r) := by
    rw [abs_mul, abs_of_pos (mul_pos hX0 hL)]
    calc
      _ ≤ X * L * (3 / (2 * t ^ 3)) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = 3 * L / (2 * r * u ^ 3) := by
        dsimp [t]
        field_simp [hr.ne', hu.ne']
        nlinarith [congrArg (fun x : ℝ => x * (L * u ^ 3)) hr2]
      _ ≤ 12 * L / (a ^ 3 * r) := by
        have hp := pow_le_pow_left₀ (by positivity : 0 ≤ a / 2) hutwo 3
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hp)]
  have hlogt : log t = L / 2 + log u := by
    rw [show t = r * u from rfl, log_mul hr.ne' hu.ne', log_sqrt hX0.le]
  have hidentity : X * L * secondRawMargin X t + s / a + log a =
      X * L * (log ((1 - t⁻¹ ^ 3) / (1 - t⁻¹ ^ 2)) - 1 / t ^ 2) +
        (L * (1 / u ^ 2 - 1 / 2) + s / a) - (log u - log a) := by
    unfold secondRawMargin
    rw [hlogt]
    change X * L * (_ - (L / 2 + log u) / (X * L)) + s / a + log a = _
    dsimp [t]
    field_simp [hX0.ne', hL.ne', hr.ne', hu.ne']
    nlinarith [congrArg (fun x : ℝ => x * (L * u ^ 2)) hr2]
  change |X * L * secondRawMargin X t + s / a + log a| ≤ _
  rw [hidentity]
  calc
    _ ≤ |X * L * (log ((1 - t⁻¹ ^ 3) / (1 - t⁻¹ ^ 2)) - 1 / t ^ 2)| +
        |L * (1 / u ^ 2 - 1 / 2) + s / a| + |log u - log a| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ 12 * L / (a ^ 3 * r) + 4 * K ^ 2 / L + (2 * K / a) / L := by
      linarith [hgainbound, hinvbound, hlogbound]
    _ = secondExpansionError X K := by unfold secondExpansionError; dsimp [a, L, r]; ring

private theorem second_margin_antitone {X : ℝ} (hX : 1 < X) :
    AntitoneOn (secondRawMargin X) (Set.Ioi 1) := by
  intro u hu v hv huv
  have hu0 : 0 < u := by change 1 < u at hu; linarith
  have hv0 : 0 < v := by change 1 < v at hv; linarith
  have hratio (t : ℝ) (ht : 1 < t) :
      (1 - t⁻¹ ^ 3) / (1 - t⁻¹ ^ 2) = 1 + 1 / (t * (t + 1)) := by
    have ht0 : 0 < t := by linarith
    have hi : t⁻¹ < 1 := (inv_lt_one₀ ht0).mpr ht
    have hd : 1 - t⁻¹ ^ 2 ≠ 0 :=
      (sub_pos.mpr (pow_lt_one₀ (inv_nonneg.mpr ht0.le) hi (by norm_num))).ne'
    apply (div_eq_iff hd).mpr
    field_simp [ht0.ne', (show t + 1 ≠ 0 by linarith)] <;> ring
  unfold secondRawMargin
  rw [hratio u hu, hratio v hv]
  have hden : u * (u + 1) ≤ v * (v + 1) := by nlinarith
  have harg : 1 + 1 / (v * (v + 1)) ≤ 1 + 1 / (u * (u + 1)) :=
    by linarith [one_div_le_one_div_of_le (by positivity : 0 < u * (u + 1)) hden]
  have hraw := log_le_log (by positivity : 0 < 1 + 1 / (v * (v + 1))) harg
  have hlog := log_le_log hu0 huv
  have hprice := div_le_div_of_nonneg_right hlog
    (mul_pos (by linarith : 0 < X) (log_pos hX)).le
  linarith

private theorem second_loss_occupancy {X : ℝ} (hX : 1 < X) {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime)
    (hanti : ∀ q r : ℕ, q.Prime → r.Prime → q < r →
      n.factorization r ≤ n.factorization q) :
    layerLoss X n p 2 =
      if p ≤ layerPrime n 2 then max (-secondRawMargin X p) 0
      else max (secondRawMargin X p) 0 := by
  have hiff : 2 ≤ n.factorization p ↔ p ≤ layerPrime n 2 := by
    constructor
    · intro hv
      by_contra! hq
      have := valuation_above_layer_prime hn (by norm_num : 1 ≤ (2 : ℕ)) hp hq
      omega
    · exact valuation_below_layer_prime hp hanti
  unfold layerLoss
  rw [second_margin_at_prime X hp]
  by_cases h : p ≤ layerPrime n 2
  · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
    by_cases hg : 0 ≤ secondRawMargin X p
    · simp [max_eq_left hg, max_eq_right (neg_nonpos.mpr hg)]
    · have hg' : secondRawMargin X p ≤ 0 := le_of_not_ge hg
      simp [max_eq_right hg', max_eq_left (neg_nonneg.mpr hg')]
  · rw [ite_eq_right h, ite_eq_right (fun hv => h (hiff.mp hv)), sub_zero]

/-- A finite, literal residual bound for the complete second layer. The analytic
and theta premises are explicit finite tail conditions; they are not a pressure
or defect hypothesis. Both endpoint losses vanish, even at prime endpoints.
The still-unproved uniform full residual target is not weakened to this statement. -/
theorem finite_actual_second_layer_tube_bound {X δ : ℝ} {n : ℕ}
    (hX : 1 < X) (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      n.factorization q ≤ n.factorization p)
    (hlarge : 2 * (|secondTubeCenter| + 1) ≤ sqrt 2 * log X)
    (hrem : secondExpansionError X (|secondTubeCenter| + 1) ≤ δ / (2 * sqrt 2))
    (hA : sqrt X < secondTubePoint X (secondTubeCenter - δ))
    (hQlo : secondTubePoint X (secondTubeCenter - δ) < (layerPrime n 2 : ℝ))
    (hQhi : (layerPrime n 2 : ℝ) < secondTubePoint X (secondTubeCenter + δ))
    (hθlo : |Chebyshev.theta (secondTubePoint X (secondTubeCenter - δ)) -
      secondTubePoint X (secondTubeCenter - δ)| ≤ δ * sqrt X / (2 * log X))
    (hθhi : |Chebyshev.theta (secondTubePoint X (secondTubeCenter + δ)) -
      secondTubePoint X (secondTubeCenter + δ)| ≤ δ * sqrt X / (2 * log X)) :
    0 ≤ sqrt X * log X ^ 3 *
      (actualDefect X n - completeFirstLayerLoss X n - completeHigherLayerLoss X n) ∧
    sqrt X * log X ^ 3 *
      (actualDefect X n - completeFirstLayerLoss X n - completeHigherLayerLoss X n) ≤
        9 * δ ^ 2 / sqrt 2 := by
  classical
  let a := sqrt (2 : ℝ)
  let L := log X
  let r := sqrt X
  let A := secondTubePoint X (secondTubeCenter - δ)
  let B := secondTubePoint X (secondTubeCenter + δ)
  let S := lossPrimes X n
  let W := Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊
  have ha : 0 < a := sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 2 := sq_sqrt (by norm_num)
  have hL : 0 < L := log_pos hX
  have hr : 0 < r := sqrt_pos.mpr (by linarith : 0 < X)
  have hr2 : r ^ 2 = X := sq_sqrt (by linarith)
  have hr1 : 1 < r := by nlinarith
  have hA1 : 1 < A := hr1.trans hA
  have hAB : A < B := hQlo.trans hQhi
  have hB1 : 1 < B := hA1.trans hAB
  have hcenter : secondTubeCenter / a + log a = 0 := by
    rw [show log a = log 2 / 2 by exact log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    unfold secondTubeCenter
    field_simp [ha.ne']
    nlinarith [congrArg (fun t : ℝ => log 2 * t) ha2]
  have hslo : |secondTubeCenter - δ| ≤ |secondTubeCenter| + 1 :=
    (abs_sub _ _).trans (by rw [abs_of_pos hδ]; linarith)
  have hshi : |secondTubeCenter + δ| ≤ |secondTubeCenter| + 1 :=
    (abs_add_le _ _).trans (by rw [abs_of_pos hδ]; linarith)
  have elo := (compact_second_raw_margin hX (by positivity : 0 ≤ |secondTubeCenter| + 1)
    hslo hlarge hA1).trans hrem
  have ehi := (compact_second_raw_margin hX (by positivity : 0 ≤ |secondTubeCenter| + 1)
    hshi hlarge hB1).trans hrem
  have emlo : |X * L * secondRawMargin X A - δ / a| ≤ δ / (2 * a) := by
    change |X * L * secondRawMargin X A + (secondTubeCenter - δ) / a + log a| ≤
      δ / (2 * a) at elo
    have heq : X * L * secondRawMargin X A + (secondTubeCenter - δ) / a + log a =
        X * L * secondRawMargin X A - δ / a := by
      calc
        _ = X * L * secondRawMargin X A + (secondTubeCenter / a + log a) - δ / a := by ring
        _ = _ := by rw [hcenter]; ring
    rwa [heq] at elo
  have emhi : |X * L * secondRawMargin X B + δ / a| ≤ δ / (2 * a) := by
    change |X * L * secondRawMargin X B + (secondTubeCenter + δ) / a + log a| ≤
      δ / (2 * a) at ehi
    have heq : X * L * secondRawMargin X B + (secondTubeCenter + δ) / a + log a =
        X * L * secondRawMargin X B + δ / a := by
      calc
        _ = X * L * secondRawMargin X B + (secondTubeCenter / a + log a) + δ / a := by ring
        _ = _ := by rw [hcenter]; ring
    rwa [heq] at ehi
  have hXL : 0 < X * L := mul_pos (by linarith) hL
  have hmarginA : 0 < secondRawMargin X A := by
    have := (abs_le.mp emlo).1
    have hδa : 0 < δ / (2 * a) := by positivity
    have heq : δ / a = 2 * (δ / (2 * a)) := by ring
    have hprod : 0 < X * L * secondRawMargin X A := by linarith
    exact (mul_pos_iff_of_pos_left hXL).mp hprod
  have hmarginB : secondRawMargin X B < 0 := by
    have := (abs_le.mp emhi).2
    have hδa : 0 < δ / (2 * a) := by positivity
    have heq : δ / a = 2 * (δ / (2 * a)) := by ring
    have hprod : X * L * secondRawMargin X B < 0 := by linarith
    by_contra! hnot
    nlinarith [mul_nonneg hXL.le hnot]
  have hmargin (p : ℕ) (hpA : A < (p : ℝ)) (hpB : (p : ℝ) ≤ B) :
      |secondRawMargin X p| ≤ 3 * δ / (2 * a * X * L) := by
    have hAp := second_margin_antitone hX (show A ∈ Set.Ioi 1 from hA1)
      (show (p : ℝ) ∈ Set.Ioi 1 from hA1.trans hpA) hpA.le
    have hpB' := second_margin_antitone hX
      (show (p : ℝ) ∈ Set.Ioi 1 from hA1.trans hpA)
      (show B ∈ Set.Ioi 1 from hB1) hpB
    have hlo := (abs_le.mp emhi).1
    have hhi := (abs_le.mp emlo).2
    have hhalf : δ / a = 2 * (δ / (2 * a)) := by ring
    have hthree : 3 * δ / (2 * a) = 3 * (δ / (2 * a)) := by ring
    have hform : 3 * δ / (2 * a * X * L) = (3 * δ / (2 * a)) / (X * L) := by ring
    rw [hform, abs_le]
    constructor
    · rw [← neg_div]
      apply (div_le_iff₀ hXL).mpr
      have hm := mul_le_mul_of_nonneg_left hpB' hXL.le
      nlinarith
    · apply (le_div_iff₀ hXL).mpr
      have hm := mul_le_mul_of_nonneg_left hAp hXL.le
      nlinarith
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hmemW (p : ℕ) : p ∈ W ↔ p.Prime ∧ A < (p : ℝ) ∧ (p : ℝ) ≤ B := by
    simp only [W, Finset.mem_sdiff, Nat.mem_primesLE]
    rw [Nat.le_floor_iff (by linarith : 0 ≤ B), Nat.le_floor_iff (by linarith : 0 ≤ A)]
    constructor
    · rintro ⟨⟨hpB, hp⟩, hn⟩
      exact ⟨hp, lt_of_not_ge (fun h => hn ⟨h, hp⟩), hpB⟩
    · rintro ⟨hp, hpA, hpB⟩
      exact ⟨⟨hpB, hp⟩, fun h => hpA.not_ge h.1⟩
  have hzero (p : ℕ) (hp : p ∈ S) (hpW : p ∉ W) : layerLoss X n p 2 = 0 := by
    have hpp := hprime p hp
    have hcases : (p : ℝ) ≤ A ∨ B ≤ (p : ℝ) := by
      by_contra! hnot
      exact hpW ((hmemW p).mpr ⟨hpp, hnot.1, hnot.2.le⟩)
    rw [second_loss_occupancy hX (by omega : 0 < n) hpp hanti]
    rcases hcases with hpa | hbp
    · have hpQ : p ≤ layerPrime n 2 := by exact_mod_cast hpa.trans hQlo.le
      rw [ite_eq_left hpQ]
      have hm := second_margin_antitone hX
        (show (p : ℝ) ∈ Set.Ioi 1 by change (1 : ℝ) < p; exact_mod_cast hpp.one_lt)
        (show A ∈ Set.Ioi 1 from hA1) hpa
      exact max_eq_right (by linarith)
    · have hpQ : ¬ p ≤ layerPrime n 2 := by
        have hh : (layerPrime n 2 : ℝ) < p := hQhi.trans_le hbp
        exact not_le_of_gt (by exact_mod_cast hh)
      rw [ite_eq_right hpQ]
      have hm := second_margin_antitone hX
        (show B ∈ Set.Ioi 1 from hB1)
        (show (p : ℝ) ∈ Set.Ioi 1 by change (1 : ℝ) < p; exact_mod_cast hpp.one_lt) hbp
      exact max_eq_right (by linarith)
  have hθmass : Chebyshev.theta B - Chebyshev.theta A ≤ 3 * δ * r / L := by
    have hwidth : B - A = 2 * δ * r / L := by
      dsimp [A, B, secondTubePoint, r, L]
      ring
    have hlo := (abs_le.mp hθlo).1
    have hhi := (abs_le.mp hθhi).2
    change -(δ * r / (2 * L)) ≤ Chebyshev.theta A - A at hlo
    change Chebyshev.theta B - B ≤ δ * r / (2 * L) at hhi
    have heq : δ * r / (2 * L) = δ * r / L / 2 := by ring
    calc
      _ ≤ B - A + 2 * (δ * r / (2 * L)) := by linarith only [hlo, hhi]
      _ = 3 * δ * r / L := by rw [hwidth]; ring
  have hsumW : (∑ p ∈ W, log p) = Chebyshev.theta B - Chebyshev.theta A := by
    have hsub : Nat.primesLE ⌊A⌋₊ ⊆ Nat.primesLE ⌊B⌋₊ := by
      intro p hp
      obtain ⟨hpa, hpp⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by linarith : 0 ≤ B)).mpr
        (((Nat.le_floor_iff (by linarith : 0 ≤ A)).mp hpa).trans hAB.le), hpp⟩
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    have hh := sum_sdiff hsub (f := fun p : ℕ => log (p : ℝ))
    dsimp [W]
    linarith
  have hcount : (W.card : ℝ) ≤ 6 * δ * r / L ^ 2 := by
    have hlower : (W.card : ℝ) * (L / 2) ≤ ∑ p ∈ W, log p := by
      calc
        _ = ∑ _p ∈ W, L / 2 := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro p hp
          have hh := (hmemW p).mp hp
          have hlog := log_le_log hr (hA.trans hh.2.1).le
          rw [show log r = L / 2 from log_sqrt (by linarith : 0 ≤ X)] at hlog
          exact hlog
    rw [hsumW] at hlower
    have hb := hlower.trans hθmass
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hm := (mul_le_mul_of_nonneg_right hb hL.le)
    field_simp [hL.ne'] at hm
    nlinarith
  have hC2 : completeSecondLayerLoss X n ≤
      (W.card : ℝ) * (3 * δ / (2 * a * X * L)) := by
    have hbound0 : 0 ≤ 3 * δ / (2 * a * X * L) := by positivity
    have hterms (p : ℕ) (hp : p ∈ S) :
        layerLoss X n p 2 ≤ if p ∈ W then 3 * δ / (2 * a * X * L) else 0 := by
      by_cases hpW : p ∈ W
      · rw [ite_eq_left hpW]
        have hh := (hmemW p).mp hpW
        have hloss : layerLoss X n p 2 ≤ |secondRawMargin X p| := by
          rw [second_loss_occupancy hX (by omega : 0 < n) hh.1 hanti]
          split_ifs
          · exact max_le (by rw [← abs_neg (secondRawMargin X p)]; exact le_abs_self _) (abs_nonneg _)
          · exact max_le (le_abs_self _) (abs_nonneg _)
        exact hloss.trans (hmargin p hh.2.1 hh.2.2)
      · rw [ite_eq_right hpW, hzero p hp hpW]
    calc
      completeSecondLayerLoss X n = ∑ p ∈ S, layerLoss X n p 2 := rfl
      _ ≤ ∑ p ∈ S, if p ∈ W then 3 * δ / (2 * a * X * L) else 0 := sum_le_sum hterms
      _ = ∑ p ∈ S ∩ W, 3 * δ / (2 * a * X * L) := by
        rw [← sum_filter]
        congr 1
      _ ≤ ∑ p ∈ W, 3 * δ / (2 * a * X * L) :=
        sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => hbound0)
      _ = _ := by simp
  have hnonneg : 0 ≤ completeSecondLayerLoss X n :=
    sum_nonneg (fun p _ => layer_loss_nonneg X n p 2)
  have hscale : 0 ≤ r * L ^ 3 := by positivity
  have hbound : r * L ^ 3 * completeSecondLayerLoss X n ≤ 9 * δ ^ 2 / a := by
    have hc := mul_le_mul_of_nonneg_right hcount
      (by positivity : 0 ≤ 3 * δ / (2 * a * X * L))
    have hb := mul_le_mul_of_nonneg_left (hC2.trans hc) hscale
    have heq : r * L ^ 3 * ((6 * δ * r / L ^ 2) * (3 * δ / (2 * a * X * L))) =
        9 * δ ^ 2 / a := by
      field_simp [ha.ne', hL.ne', (show X ≠ 0 by linarith)]
      nlinarith [congrArg (fun t : ℝ => 9 * δ ^ 2 * L ^ 3 * t) hr2]
    simpa only [heq] using hb
  have hsplit := actual_defect_decomposition hX hn
  have hres : actualDefect X n - completeFirstLayerLoss X n - completeHigherLayerLoss X n =
      completeSecondLayerLoss X n := by linarith
  rw [hres]
  exact ⟨mul_nonneg hscale hnonneg, hbound⟩

/- Fixed endpoints are taken AFTER fixing δ. These limits concern real X,
not primes in an assumed short interval. -/
private theorem tube_endpoint_limits (s : ℝ) :
    Tendsto (fun X : ℝ => secondTubePoint X s) atTop atTop ∧
    Tendsto (fun X : ℝ => secondTubePoint X s / sqrt X) atTop (𝓝 (sqrt 2)) ∧
    Tendsto (fun X : ℝ => log X / log (secondTubePoint X s)) atTop (𝓝 2) := by
  have ha : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hu : Tendsto (fun X : ℝ => sqrt 2 + s / log X) atTop (𝓝 (sqrt 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop tendsto_log_atTop)
  have ht : Tendsto (fun X : ℝ => secondTubePoint X s) atTop atTop := by
    simpa only [secondTubePoint, mul_comm] using hu.pos_mul_atTop ha tendsto_sqrt_atTop
  have hr : Tendsto (fun X : ℝ => secondTubePoint X s / sqrt X)
      atTop (𝓝 (sqrt 2)) := by
    apply hu.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    dsimp [secondTubePoint]
    field_simp [(sqrt_pos.mpr hX).ne'] <;> ring
  have hlog : Tendsto (fun X : ℝ => log (secondTubePoint X s) / log X)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hh := (hu.log ha.ne').div_atTop tendsto_log_atTop
    have hh' := hh.add_const (1 / 2 : ℝ)
    simp only [zero_add] at hh'
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hu.eventually (eventually_gt_nhds ha)] with X hX huX
    rw [secondTubePoint, log_mul (sqrt_pos.mpr (by linarith)).ne' huX.ne',
      log_sqrt (by linarith : 0 ≤ X)]
    field_simp [(log_pos hX).ne'] <;> ring
  refine ⟨ht, hr, ?_⟩
  convert hlog.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1 <;> simp [inv_div]

private theorem theta_error_at_tube (s : ℝ) :
    Tendsto (fun X : ℝ => (log X / sqrt X) *
      (Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s))
      atTop (𝓝 0) := by
  obtain ⟨ht, hr, hlogs⟩ := tube_endpoint_limits s
  have he := (theta_error_log_power 1).tendsto_div_nhds_zero.comp ht
  have hh := (he.mul hr).mul hlogs
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually_gt_atTop 1] with X hX htX
  dsimp only [Function.comp_def]
  simp only [pow_one]
  field_simp [(show secondTubePoint X s ≠ 0 by linarith),
    (log_pos htX).ne', (sqrt_pos.mpr (by linarith : 0 < X)).ne'] <;> ring

private theorem second_expansion_error_limit (K : ℝ) :
    Tendsto (fun X : ℝ => secondExpansionError X K) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun X : ℝ => log X / sqrt X) atTop (𝓝 0) := by
    simpa only [rpow_one, sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hfirst : Tendsto (fun X : ℝ => (4 * K ^ 2 + 2 * K / sqrt 2) / log X)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hsecond := hsmall.const_mul (12 / sqrt (2 : ℝ) ^ 3)
  have hh := hfirst.add hsecond
  simp only [mul_zero, add_zero] at hh
  exact hh.congr (fun X => by unfold secondExpansionError; ring)

/-- G1: fixed δ, explicit compact error, geometry, and BOTH global N=1
theta errors imply the actual finite analytic hypotheses eventually. -/
private theorem fixed_tube_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop,
      1 < X ∧
      2 * (|secondTubeCenter| + 1) ≤ sqrt 2 * log X ∧
      secondExpansionError X (|secondTubeCenter| + 1) ≤ δ / (2 * sqrt 2) ∧
      sqrt X < secondTubePoint X (secondTubeCenter - δ) ∧
      |Chebyshev.theta (secondTubePoint X (secondTubeCenter - δ)) -
        secondTubePoint X (secondTubeCenter - δ)| ≤ δ * sqrt X / (2 * log X) ∧
      |Chebyshev.theta (secondTubePoint X (secondTubeCenter + δ)) -
        secondTubePoint X (secondTubeCenter + δ)| ≤ δ * sqrt X / (2 * log X) := by
  have ha : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have ha1 : 1 < sqrt (2 : ℝ) := by
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hu : Tendsto (fun X : ℝ => sqrt 2 + (secondTubeCenter - δ) / log X)
      atTop (𝓝 (sqrt 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop tendsto_log_atTop)
  have htheta (s : ℝ) : ∀ᶠ X : ℝ in atTop,
      |Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s| ≤
        δ * sqrt X / (2 * log X) := by
    have he := (Metric.tendsto_nhds.mp (theta_error_at_tube s)) (δ / 2) (by positivity)
    filter_upwards [eventually_gt_atTop (1 : ℝ), he] with X hX heX
    have hL : 0 < log X := log_pos hX
    have hr : 0 < sqrt X := sqrt_pos.mpr (by linarith)
    have hh : (log X / sqrt X) *
        |Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s| ≤ δ / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_mul, abs_div,
        abs_of_pos hL, abs_of_pos hr] using heX.le
    have hh' : log X *
        |Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s| ≤ δ / 2 * sqrt X := by
      exact (div_le_iff₀ hr).mp (by simpa only [div_mul_eq_mul_div] using hh)
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL)).mpr
    nlinarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop (2 * (|secondTubeCenter| + 1) / sqrt 2),
    (second_expansion_error_limit (|secondTubeCenter| + 1)).eventually
      (eventually_lt_nhds (show 0 < δ / (2 * sqrt 2) by positivity)),
    hu.eventually (eventually_gt_nhds ha1),
    htheta (secondTubeCenter - δ), htheta (secondTubeCenter + δ)]
      with X hX hlarge hrem hgeo hlo hhi
  refine ⟨hX, ?_, hrem.le, ?_, hlo, hhi⟩
  · simpa only [mul_comm] using (div_le_iff₀ ha).mp hlarge
  · unfold secondTubePoint
    exact lt_mul_of_one_lt_right (sqrt_pos.mpr (by linarith : 0 < X)) hgeo

/-- Bounded P bounds X for the original record, uniformly in its price. -/
private theorem record_prime_escape {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x) (hmu : ∀ x, 0 < mu x)
    (hrecord : ∀ x k, 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x))
    (hX : Tendsto (fun x => log (m x : ℝ)) l atTop) :
    Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop := by
  apply tendsto_atTop.mpr
  intro A
  let B : ℝ := max A 2
  have hB2 : 2 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < log (4 * B ^ 2) := log_pos (by nlinarith)
  filter_upwards [hX.eventually_ge_atTop (B * log (4 * B ^ 2) + 2)] with x hx
  by_contra! hsmall
  have hpB : (largestPrime (m x) : ℝ) ≤ B := hsmall.le.trans (le_max_left _ _)
  have hP2 : (2 : ℝ) ≤ largestPrime (m x) := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by have := hm x; omega : m x ≠ 1)
    exact_mod_cast hp.two_le.trans
      (le_sup (f := id) (hp.mem_primeFactors hpd (by have := hm x; omega : m x ≠ 0)))
  have hp0 : (0 : ℝ) ≤ largestPrime (m x) := by linarith
  have hlogle : log (4 * (largestPrime (m x) : ℝ) ^ 2) ≤ log (4 * B ^ 2) :=
    log_le_log (by positivity)
      (by nlinarith [pow_le_pow_left₀ hp0 hpB 2])
  have hmass := record_log_envelope (hm x) (hmu x) (hrecord x)
  have hbounded : log (m x : ℝ) ≤ B * log (4 * B ^ 2) := hmass.trans
    ((mul_le_mul_of_nonneg_left hlogle hp0).trans
      (mul_le_mul_of_nonneg_right hpB hlogB.le))
  linarith

/-- G2: the COMPLETE higher finite envelope, at the critical normalization,
tends to zero on every record family whose ORIGINAL logarithmic clock escapes.
R is chosen from X, not postulated as a prime/exponent cap. -/
private theorem higher_layer_negligible {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x) (hmu : ∀ x, 0 < mu x)
    (hrecord : ∀ x k, 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x))
    (hX : Tendsto (fun x => log (m x : ℝ)) l atTop)
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => sqrt (log (m x : ℝ)) * log (log (m x : ℝ)) ^ 3 *
      completeHigherLayerLoss (log (m x : ℝ)) (m x)) l (𝓝 0) := by
  let X : α → ℝ := fun x => log (m x : ℝ)
  let P : α → ℝ := fun x => largestPrime (m x)
  let Q : α → ℝ := fun x => layerPrime (m x) 3
  let R : α → ℝ := fun x => (X x * log (X x) / log 2) ^ (1 / 3 : ℝ)
  let E : α → ℝ := fun x => sqrt (X x) * log (X x) ^ 3 *
    (2 * R x / P x + referencePrice (X x) * (Q x * log (4 * P x ^ 2)))
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2le : log (2 : ℝ) ≤ 1 := by
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hL : Tendsto (fun x => log (X x)) l atTop := tendsto_log_atTop.comp hX
  have hXP : Tendsto (fun x => X x / P x) l (𝓝 1) :=
    (record_mass_limits m mu hm hmu hrecord hP).2.2.1
  have hQ3 : Tendsto (fun x => Q x ^ 3 / P x) l (𝓝 3) :=
    record_layer_ratio m mu hm hmu hrecord hP 3 (by norm_num)
  have hsmall : Tendsto (fun x => log (X x) / X x ^ (1 / 4 : ℝ)) l (𝓝 0) := by
    simpa only [rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp hX)
  have hmajor : Tendsto (fun x => 8 * (log (X x) ^ 3 / X x ^ (1 / 12 : ℝ)))
      l (𝓝 0) := by
    have hh := ((isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 12)).tendsto_div_nhds_zero.comp hX).const_mul 8
    simpa only [rpow_natCast, rpow_ofNat, Function.comp_def, mul_zero] using hh
  have hregime : ∀ᶠ x in l,
      1 < X x ∧ 1 ≤ R x ∧ R x < P x ∧
      X x * log (X x) = log 2 * R x ^ 3 ∧
      0 ≤ E x ∧ E x ≤ 8 * (log (X x) ^ 3 / X x ^ (1 / 12 : ℝ)) := by
    filter_upwards [hX.eventually_gt_atTop 4, hL.eventually_ge_atTop 1,
      hP.eventually_gt_atTop 0,
      hXP.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hXP.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)),
      hQ3.eventually (eventually_lt_nhds (by norm_num : (3 : ℝ) < 4)),
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hX).eventually_ge_atTop 8,
      hsmall.eventually (eventually_lt_nhds hlog2)]
        with x hx hLx hp hlow hhigh hq hpow hlogs
    change 4 < X x at hx
    change 0 < P x at hp
    change 8 ≤ X x ^ (1 / 4 : ℝ) at hpow
    have hx0 : 0 < X x := by linarith
    have hL0 : 0 < log (X x) := by linarith
    have hcomp : X x / 2 ≤ P x ∧ P x ≤ 2 * X x := by
      constructor
      · have hh := (div_lt_iff₀ hp).mp hhigh
        linarith
      · have hh := (lt_div_iff₀ hp).mp hlow
        linarith
    let C : ℝ := X x ^ (5 / 12 : ℝ)
    have hC0 : 0 ≤ C := rpow_nonneg hx0.le _
    have hCcube : C ^ 3 = X x * X x ^ (1 / 4 : ℝ) := by
      dsimp [C]
      rw [← rpow_mul_natCast hx0.le]
      have he : (5 / 12 : ℝ) * (3 : ℕ) = 1 + (1 / 4 : ℝ) := by norm_num
      rw [he, rpow_add hx0, rpow_one]
    have hbase : 0 < X x * log (X x) / log 2 := by positivity
    have hR0 : 0 ≤ R x := rpow_nonneg hbase.le _
    have hRcube : R x ^ 3 = X x * log (X x) / log 2 := by
      dsimp [R]
      rw [← rpow_mul_natCast hbase.le]
      norm_num
    have hclock : X x * log (X x) = log 2 * R x ^ 3 := by
      rw [hRcube]
      field_simp [hlog2.ne'] <;> ring
    have hR1 : 1 ≤ R x := by
      have hb : 1 ≤ X x * log (X x) / log 2 := by
        apply (le_div_iff₀ hlog2).mpr
        nlinarith [mul_le_mul_of_nonneg_left hLx hx0.le]
      have hh := rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hb
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
      simpa only [one_rpow] using hh
    have hRC : R x ≤ C := by
      have hb : log (X x) / log 2 ≤ X x ^ (1 / 4 : ℝ) := by
        apply (div_le_iff₀ hlog2).mpr
        have hh := (div_lt_iff₀ (rpow_pos_of_pos hx0 (1 / 4 : ℝ))).mp hlogs
        linarith
      have hh : R x ^ 3 ≤ C ^ 3 := by
        rw [hRcube, hCcube, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hb hx0.le
      by_contra! hnot
      exact (not_lt_of_ge hh) (pow_lt_pow_left₀ hnot hC0 (by norm_num : (3 : ℕ) ≠ 0))
    have hQC : Q x ≤ C := by
      have hh : Q x ^ 3 ≤ C ^ 3 := by
        rw [hCcube]
        have hq' : Q x ^ 3 < 4 * P x := (div_lt_iff₀ hp).mp hq
        calc
          Q x ^ 3 ≤ 4 * P x := hq'.le
          _ ≤ 8 * X x := by linarith only [hcomp.2]
          _ ≤ X x * X x ^ (1 / 4 : ℝ) := by
            nlinarith only [mul_le_mul_of_nonneg_left hpow hx0.le]
      by_contra! hnot
      exact (not_lt_of_ge hh) (pow_lt_pow_left₀ hnot hC0 (by norm_num : (3 : ℕ) ≠ 0))
    have hCsqrt : C ≤ sqrt (X x) := by
      rw [sqrt_eq_rpow]
      exact rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (5 / 12 : ℝ) ≤ 1 / 2)
    have hsqrt : sqrt (X x) < X x / 2 := by
      have hr2 : 2 < sqrt (X x) := by
        nlinarith [sq_sqrt hx0.le, sqrt_nonneg (X x)]
      nlinarith [sq_sqrt hx0.le,
        mul_pos (sqrt_pos.mpr hx0) (sub_pos.mpr hr2)]
    have hRP : R x < P x := (hRC.trans hCsqrt).trans_lt (hsqrt.trans_le hcomp.1)
    have hlogB0 : 0 ≤ log (4 * P x ^ 2) := by
      apply log_nonneg
      nlinarith [hcomp.1]
    have hlogB : log (4 * P x ^ 2) ≤ 4 * log (X x) := by
      have hb : log (4 * P x ^ 2) ≤ log (16 * X x ^ 2) :=
        log_le_log (by positivity) (by
          nlinarith [pow_le_pow_left₀ hp.le hcomp.2 2])
      have h16 : log (16 : ℝ) ≤ 2 * log (X x) := by
        have hh := log_le_log (by norm_num : (0 : ℝ) < 16)
          (show 16 ≤ X x ^ 2 by nlinarith)
        simpa only [log_pow, Nat.cast_ofNat] using hh
      rw [log_mul (by norm_num : (16 : ℝ) ≠ 0) (pow_ne_zero 2 hx0.ne'), log_pow] at hb
      norm_num only [Nat.cast_ofNat] at hb
      linarith only [hb, h16]
    have hbound : 2 * R x / P x + referencePrice (X x) * (Q x * log (4 * P x ^ 2)) ≤
        8 * C / X x := by
      have hfirst : 2 * R x / P x ≤ 4 * C / X x := by
        apply (div_le_div_iff₀ hp hx0).mpr
        nlinarith [mul_le_mul_of_nonneg_left hcomp.1 (show 0 ≤ 4 * C by positivity),
          mul_le_mul_of_nonneg_right hRC hx0.le]
      have hsecond : referencePrice (X x) * (Q x * log (4 * P x ^ 2)) ≤ 4 * C / X x := by
        have hb : Q x * log (4 * P x ^ 2) ≤ C * (4 * log (X x)) :=
          (mul_le_mul_of_nonneg_right hQC hlogB0).trans
            (mul_le_mul_of_nonneg_left hlogB hC0)
        have hh := mul_le_mul_of_nonneg_left hb (reference_price_pos (by linarith : 1 < X x)).le
        convert hh using 1 <;> unfold referencePrice <;> field_simp [hx0.ne', hL0.ne'] <;> ring
      calc
        _ ≤ 4 * C / X x + 4 * C / X x := add_le_add hfirst hsecond
        _ = 8 * C / X x := by ring
    have hscale : 0 ≤ sqrt (X x) * log (X x) ^ 3 := by positivity
    have hnorm : sqrt (X x) * log (X x) ^ 3 * (8 * C / X x) =
        8 * (log (X x) ^ 3 / X x ^ (1 / 12 : ℝ)) := by
      have he : sqrt (X x) * C * X x ^ (1 / 12 : ℝ) = X x := by
        dsimp [C]
        rw [sqrt_eq_rpow, ← rpow_add hx0, ← rpow_add hx0]
        norm_num
      field_simp [hx0.ne', (rpow_pos_of_pos hx0 (1 / 12 : ℝ)).ne']
      nlinarith [congrArg (fun z : ℝ => 8 * log (X x) ^ 3 * z) he]
    refine ⟨by linarith, hR1, hRP, hclock, ?_, ?_⟩
    · dsimp [E]
      exact mul_nonneg hscale (add_nonneg (by positivity)
        (mul_nonneg (reference_price_pos (by linarith : 1 < X x)).le
          (mul_nonneg (Nat.cast_nonneg _) hlogB0)))
    · dsimp [E]
      exact (mul_le_mul_of_nonneg_left hbound hscale).trans_eq hnorm
  -- The actual finite envelope itself tends to zero; no assumed loss bound.
  have hEnv : Tendsto E l (𝓝 0) := squeeze_zero'
    (hregime.mono fun _ h => h.2.2.2.2.1)
    (hregime.mono fun _ h => h.2.2.2.2.2) hmajor
  apply squeeze_zero' _ _ hEnv
  · filter_upwards [hregime] with x hx
    have hfin := finite_complete_higher_layer_bound hx.1 (hm x) (hmu x) (hrecord x)
      hx.2.1 hx.2.2.1 hx.2.2.2.1.le
    exact mul_nonneg (mul_nonneg (sqrt_nonneg _) (pow_nonneg (log_nonneg hx.1.le) 3)) hfin.1
  · filter_upwards [hregime] with x hx
    have hfin := finite_complete_higher_layer_bound hx.1 (hm x) (hmu x) (hrecord x)
      hx.2.1 hx.2.2.1 hx.2.2.2.1.le
    exact mul_le_mul_of_nonneg_left hfin.2.2
      (mul_nonneg (sqrt_nonneg _) (pow_nonneg (log_nonneg hx.1.le) 3))

/-- Uniform critical residual beyond the COMPLETE first layer, on the literal
original integer and every arbitrary positive original record price. The one
threshold precedes BOTH m and mu. No first-layer or total-defect bound is assumed. -/
theorem actual_record_critical_residual :
    ∀ ε : ℝ, 0 < ε → ∃ X0 : ℝ, 1 < X0 ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective mu k < goldenResourceObjective mu m) →
      X0 ≤ log (m : ℝ) →
      let X := log (m : ℝ)
      0 ≤ sqrt X * log X ^ 3 * (actualDefect X m - completeFirstLayerLoss X m) ∧
      sqrt X * log X ^ 3 * (actualDefect X m - completeFirstLayerLoss X m) < ε := by
  intro ε hε
  classical
  let a : ℝ := sqrt 2
  let δ : ℝ := min 1 (sqrt (a * ε / 36))
  have ha : 0 < a := sqrt_pos.mpr (by norm_num)
  have hb : 0 < a * ε / 36 := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (sqrt_pos.mpr hb)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδsq : δ ^ 2 ≤ a * ε / 36 := by
    have hle : δ ≤ sqrt (a * ε / 36) := min_le_right _ _
    have hh := pow_le_pow_left₀ hδ.le hle 2
    simpa only [sq_sqrt hb.le] using hh
  have hbudget : 9 * δ ^ 2 / a ≤ ε / 4 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ k : ℕ, 0 < k → k < v.1 →
      goldenResourceObjective v.2 k < goldenResourceObjective v.2 v.1}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let X : S → ℝ := fun x => log (m x : ℝ)
  let l : Filter S := comap X atTop
  have hX : Tendsto X l atTop := tendsto_comap
  have hm (x : S) : 2 ≤ m x := x.2.1
  have hmu (x : S) : 0 < mu x := x.2.2.1
  have hrecord (x : S) (k : ℕ) : 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x) := x.2.2.2 k
  have hP := record_prime_escape m mu hm hmu hrecord hX
  have hQ := record_second_own_clock_limit m mu hm hmu hrecord hP
  have hQtube := (Metric.tendsto_nhds.mp hQ) δ hδ
  have hthird := higher_layer_negligible m mu hm hmu hrecord hX hP
  have hthirdSmall := (Metric.tendsto_nhds.mp hthird) (ε / 2) (by positivity)
  -- δ was fixed before this real analytic tail and before the record tails.
  have hanalytic := hX.eventually (fixed_tube_eventually hδ)
  have hall : ∀ᶠ x in l,
      0 ≤ sqrt (X x) * log (X x) ^ 3 *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) ∧
      sqrt (X x) * log (X x) ^ 3 *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) < ε := by
    filter_upwards [hanalytic, hQtube, hthirdSmall] with x hx hqx htx
    obtain ⟨hx1, hlarge, hrem, hA, hθlo, hθhi⟩ := hx
    have hL : 0 < log (X x) := log_pos hx1
    have hr : 0 < sqrt (X x) := sqrt_pos.mpr (by linarith)
    have hq : |log (X x) * ((layerPrime (m x) 2 : ℝ) / sqrt (X x) - sqrt 2) -
        secondTubeCenter| < δ := by
      simpa only [Real.dist_eq, secondTubeCenter, sub_neg_eq_add, X, m] using hqx
    have hQlo : secondTubePoint (X x) (secondTubeCenter - δ) < (layerPrime (m x) 2 : ℝ) := by
      have hh : (secondTubeCenter - δ) / log (X x) <
          (layerPrime (m x) 2 : ℝ) / sqrt (X x) - sqrt 2 := by
        apply (div_lt_iff₀ hL).mpr
        nlinarith [(abs_lt.mp hq).1]
      have hh' : sqrt 2 + (secondTubeCenter - δ) / log (X x) <
          (layerPrime (m x) 2 : ℝ) / sqrt (X x) := by linarith
      have hh'' := (lt_div_iff₀ hr).mp hh'
      simpa only [secondTubePoint, mul_comm] using hh''
    have hQhi : (layerPrime (m x) 2 : ℝ) < secondTubePoint (X x) (secondTubeCenter + δ) := by
      have hh : (layerPrime (m x) 2 : ℝ) / sqrt (X x) - sqrt 2 <
          (secondTubeCenter + δ) / log (X x) := by
        apply (lt_div_iff₀ hL).mpr
        nlinarith [(abs_lt.mp hq).2]
      have hh' : (layerPrime (m x) 2 : ℝ) / sqrt (X x) <
          sqrt 2 + (secondTubeCenter + δ) / log (X x) := by linarith
      have hh'' := (div_lt_iff₀ hr).mp hh'
      simpa only [secondTubePoint, mul_comm] using hh''
    have hsecond := finite_actual_second_layer_tube_bound hx1 (by have := hm x; omega : 1 ≤ m x)
      hδ hδ1 (price_record_prime_structure (hm x) (hmu x) (hrecord x)).1
      hlarge hrem hA hQlo hQhi hθlo hθhi
    have hscale : 0 ≤ sqrt (X x) * log (X x) ^ 3 := by positivity
    have hD0 : 0 ≤ sqrt (X x) * log (X x) ^ 3 * completeHigherLayerLoss (X x) (m x) :=
      mul_nonneg hscale (sum_nonneg fun p _ => sum_nonneg fun j _ =>
        layer_loss_nonneg (X x) (m x) p j)
    have hDsmall : sqrt (X x) * log (X x) ^ 3 * completeHigherLayerLoss (X x) (m x) < ε / 2 := by
      exact (le_abs_self _).trans_lt (by
        simpa only [Real.dist_eq, sub_zero, X, m] using htx)
    have hid : sqrt (X x) * log (X x) ^ 3 *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) =
        sqrt (X x) * log (X x) ^ 3 *
          (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x) -
            completeHigherLayerLoss (X x) (m x)) +
        sqrt (X x) * log (X x) ^ 3 * completeHigherLayerLoss (X x) (m x) := by ring
    rw [hid]
    constructor
    · exact add_nonneg hsecond.1 hD0
    · have hsecond' := hsecond.2
      change _ ≤ 9 * δ ^ 2 / a at hsecond'
      linarith
  -- Filter extraction selects ONE own-X threshold before any record pair.
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn price hprice hrec hlarge
  let x : S := ⟨(n, price), hn, hprice, hrec⟩
  have hx := hB (log (n : ℝ)) ((le_max_left B 2).trans hlarge) x rfl
  simpa only [X, m] using hx

end D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
