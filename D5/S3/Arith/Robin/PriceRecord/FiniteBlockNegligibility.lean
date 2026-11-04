/- GID: D5/S3/Arith/Robin/PriceRecord/FiniteBlockNegligibility
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FiniteBlockNegligibility
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Uniformly negligible finite prime-block tails on actual price records. -/

import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
import D5.S3.Arith.GoldenLayerMarginalDecay

/-! Fixed finite prime-block tails from fixed-layer rigidity and one donor exchange. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FiniteBlockNegligibility

open Finset
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime layerTail layer_tail_nonneg)

/-- A fixed finite prime block is uniformly o(1/P) over all full predecessor
records at positive prices, where P is the largest prime factor. -/
theorem price_record_finite_prime_block_negligible
    (S : Finset Nat) (hS : ∀ p ∈ S, Nat.Prime p)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ T : Real, 0 < T ∧ ∀ m : Nat, 2 ≤ m →
      ∀ lambda : Real, 0 < lambda →
      (∀ n : Nat, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : Real) →
      (largestPrime m : Real) * (∑ p ∈ S, layerTail m p) < epsilon := by
  classical
  obtain ⟨j, hjlarge⟩ := exists_nat_gt (max (1 : ℝ) (4 / epsilon))
  have hjone : 1 < (j : ℝ) := (le_max_left _ _).trans_lt hjlarge
  have hj : 2 ≤ j := by
    have h : 1 < j := by exact_mod_cast hjone
    omega
  have hjpos : (0 : ℝ) < j := by linarith
  have hjepsilon : 4 / (j : ℝ) < epsilon := by
    have h := (div_lt_iff₀ hepsilon).mp ((le_max_right _ _).trans_lt hjlarge)
    apply (div_lt_iff₀ hjpos).mpr
    nlinarith only [h]
  let Q : ℕ := ∏ p ∈ S, p
  have hQpos : 0 < Q := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hQone : 1 ≤ Q := hQpos
  obtain ⟨Tj, hTj, hrigidity⟩ :=
    price_record_fixed_layer_rigidity j hj ((j : ℝ) / 2) (by positivity)
  refine ⟨max Tj (2 * (Q : ℝ) ^ j / (j : ℝ)),
    hTj.trans_le (le_max_left _ _), ?_⟩
  intro m hm lambda hlambda hrecord hT
  let P : ℝ := largestPrime m
  let q : ℕ := layerPrime m j
  have hTjP : Tj ≤ P := (le_max_left _ _).trans hT
  have hP : 0 < P := hTj.trans_le hTjP
  have hratio := hrigidity m hm lambda hlambda hrecord hTjP
  have hlower : (j : ℝ) / 2 < (q : ℝ) ^ j / P := by
    have h := (abs_lt.mp hratio).1
    change -((j : ℝ) / 2) < (q : ℝ) ^ j / P - (j : ℝ) at h
    linarith only [h]
  have hqpower : (j : ℝ) / 2 * P < (q : ℝ) ^ j :=
    (lt_div_iff₀ hP).mp hlower
  have hQbound : 2 * (Q : ℝ) ^ j / (j : ℝ) ≤ P :=
    (le_max_right _ _).trans hT
  have hQpower : (Q : ℝ) ^ j < (q : ℝ) ^ j := by
    have h := (div_le_iff₀ hjpos).mp hQbound
    nlinarith only [h, hqpower]
  have hQq : Q < q := by
    exact_mod_cast (lt_of_pow_lt_pow_left₀ j (Nat.cast_nonneg q) hQpower)
  have hqone : 1 < q := lt_of_le_of_lt hQone hQq
  obtain ⟨hqmem, hja⟩ := layer_prime_mem hqone
  change j ≤ m.factorization q at hja
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hqmem
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hprice : 0 < lambda * (Real.log (q : ℝ) - Real.log (Q : ℝ)) := by
    apply mul_pos hlambda
    exact sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hQpos)
      (by exact_mod_cast hQq))
  have hblock := (price_record_prime_block_tail (P := q) (k := 1)
    S (by omega) hrecord hqprime hqm hS (by omega) (by simpa [Q] using hQq)).1
  simp only [pow_one, Nat.cast_one, one_mul] at hblock
  have hweighted :
      (1 / 2 : ℝ) * (∑ p ∈ S, layerTail m p) ≤
        ∑ p ∈ S, (1 - (p : ℝ)⁻¹) * layerTail m p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have hi : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa only [one_div] using (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).mpr hp2
    exact mul_le_mul_of_nonneg_right (by linarith only [hi]) (layer_tail_nonneg m (hS p hp))
  have hgain : goldenLayerMarginal q (m.factorization q) * Real.log (q : ℝ) ≤
      (q : ℝ)⁻¹ ^ j := by
    have ha : 1 ≤ m.factorization q := (show 1 ≤ j by omega).trans hja
    have hu := (le_div_iff₀ hqprime.log_pos).mp
      (golden_layer_marginal_le_inv_pow hqprime ha)
    exact hu.trans (pow_le_pow_of_le_one (inv_nonneg.mpr hqpos.le)
      ((inv_lt_one₀ hqpos).mpr (by exact_mod_cast hqprime.one_lt)).le hja)
  have htail : (∑ p ∈ S, layerTail m p) < 2 / (q : ℝ) ^ j := by
    have hg : (1 / 2 : ℝ) * (∑ p ∈ S, layerTail m p) < (q : ℝ)⁻¹ ^ j := by
      have hb : (∑ p ∈ S, (1 - (p : ℝ)⁻¹) * layerTail m p) <
          goldenLayerMarginal q (m.factorization q) * Real.log (q : ℝ) := by
        change _ + lambda * (Real.log (q : ℝ) - Real.log (Q : ℝ)) < _ at hblock
        linarith only [hblock, hprice]
      exact (hweighted.trans_lt hb).trans_le hgain
    rw [inv_pow, ← one_div] at hg
    calc
      (∑ p ∈ S, layerTail m p) < 2 * (1 / (q : ℝ) ^ j) := by linarith only [hg]
      _ = 2 / (q : ℝ) ^ j := by ring
  have hqpowpos : 0 < (q : ℝ) ^ j := pow_pos hqpos j
  have hscaled : P * (∑ p ∈ S, layerTail m p) < 4 / (j : ℝ) := by
    have hs := mul_lt_mul_of_pos_left htail hP
    have hcomp : P * (2 / (q : ℝ) ^ j) < 4 / (j : ℝ) := by
      rw [← mul_div_assoc]
      apply (div_lt_div_iff₀ hqpowpos hjpos).mpr
      nlinarith only [hqpower]
    exact hs.trans hcomp
  exact hscaled.trans hjepsilon

#print axioms price_record_finite_prime_block_negligible

end D5.S3.Arith.Robin.PriceRecord.FiniteBlockNegligibility
