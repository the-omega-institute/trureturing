/- GID: D5/S3/Arith/Robin/PriceRecord/HigherValuationTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/HigherValuationTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Uniform repeated-prime Euler-tail decay at every positive-price full record. -/

import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure

/-! The original repeated-prime tails are split at the cube root of the largest prime. -/

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.HigherValuationTail

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime layerTail)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure

/-- The complete repeated-prime Euler tail of an actual full predecessor record
has a uniform bound at every positive price, including its largest prime. -/
theorem higher_valuation_tail {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    (∑ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p), layerTail m p) ≤
      6 / (largestPrime m : ℝ) ^ (2 / 3 : ℝ) := by
  classical
  let P := largestPrime m
  let u := (P : ℝ) ^ (1 / 3 : ℝ)
  let S := m.primeFactors.filter (fun p => 2 ≤ m.factorization p)
  let small := S.filter (fun p : ℕ => (p : ℝ) ≤ u)
  let large := S.filter (fun p : ℕ => u < (p : ℝ))
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨v, hv, hvu⟩ := exists_mem_eq_sup m.primeFactors hne id
  have hPS : P ∈ m.primeFactors := by
    have heq : P = v := hvu
    exact heq.symm ▸ hv
  have hP := Nat.prime_of_mem_primeFactors hPS
  have hPm := Nat.dvd_of_mem_primeFactors hPS
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP.one_lt
  have hu0 : 0 < u := Real.rpow_pos_of_pos hP0 _
  have huP : u < (P : ℝ) := Real.rpow_lt_self_of_one_lt hP1 (by norm_num)
  have hu3 : u ^ 3 = (P : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
    norm_num
  have hu2 : u ^ 2 = (P : ℝ) ^ (2 / 3 : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
    norm_num
  have hcard : (small.card : ℝ) ≤ u := by
    have hsub : small ⊆ Ioc 0 ⌊u⌋₊ := by
      intro p hp
      obtain ⟨hpS, hpu⟩ := mem_filter.mp hp
      have hpprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hpS).1
      exact mem_Ioc.mpr ⟨hpprime.pos, Nat.le_floor hpu⟩
    calc
      _ ≤ ((Ioc 0 ⌊u⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = (⌊u⌋₊ : ℝ) := by simp
      _ ≤ u := Nat.floor_le hu0.le
  have hsmall : (∑ p ∈ small, layerTail m p) ≤ 2 / u ^ 2 := by
    have hs := sum_le_card_nsmul small (layerTail m) (2 / (P : ℝ)) (by
      intro p hp
      obtain ⟨hpS, hpu⟩ := mem_filter.mp hp
      have hpprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hpS).1
      have hpP : p < P := by exact_mod_cast hpu.trans_lt huP
      have hh := ExponentExchange.PriceRecordMissingLayer.price_record_missing_layer
        (by omega : 0 < m) hlambda hrecord hP hPm hpprime hpP
      exact hh.2.2.2.2.2.2.2.2.2.2.2.le)
    rw [nsmul_eq_mul] at hs
    calc
      _ ≤ (small.card : ℝ) * (2 / (P : ℝ)) := hs
      _ ≤ u * (2 / (P : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 / u ^ 2 := by rw [← hu3]; field_simp
  have hlarge : (∑ p ∈ large, layerTail m p) ≤ 4 / u ^ 2 := by
    have hpoint (p : ℕ) (hp : p ∈ large) : layerTail m p ≤ 2 / (p : ℝ) ^ 3 := by
      obtain ⟨hpS, _⟩ := mem_filter.mp hp
      obtain ⟨hpm, hval⟩ := mem_filter.mp hpS
      have hprime := Nat.prime_of_mem_primeFactors hpm
      have hh := actual_layer_tail_le (m := m) hprime (by norm_num : 1 ≤ (3 : ℕ))
        (by omega)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast hprime.two_le : (2 : ℝ) ≤ p)
      have hpow : (p : ℝ)⁻¹ ^ 3 ≤ 1 / 2 := by
        have hh' := pow_le_pow_of_le_one (inv_nonneg.mpr hp0.le)
          (show (p : ℝ)⁻¹ ≤ 1 by linarith) (by norm_num : 1 ≤ (3 : ℕ))
        simp only [pow_one] at hh'
        linarith
      have hb : (p : ℝ)⁻¹ ^ 3 / (1 - (p : ℝ)⁻¹ ^ 3) ≤ 2 * (p : ℝ)⁻¹ ^ 3 := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - (p : ℝ)⁻¹ ^ 3)).mpr
        nlinarith [pow_nonneg (inv_nonneg.mpr hp0.le) 3]
      simpa only [inv_pow, div_eq_mul_inv, mul_one] using hh.trans hb
    calc
      _ ≤ ∑ p ∈ large, 2 / (p : ℝ) ^ 3 := sum_le_sum hpoint
      _ = 2 * ∑ p ∈ large, 1 / (p : ℝ) ^ 3 := by simp only [mul_sum, mul_one_div]
      _ ≤ 2 * (2 / u ^ 2) := mul_le_mul_of_nonneg_left
        (finite_cubic_tail hu0 large (fun p hp => (mem_filter.mp hp).2)) (by norm_num)
      _ = 4 / u ^ 2 := by ring
  have hsplit : (∑ p ∈ S, layerTail m p) =
      (∑ p ∈ small, layerTail m p) + ∑ p ∈ large, layerTail m p := by
    simpa only [small, large, not_le] using
      (sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ u) (layerTail m)).symm
  change (∑ p ∈ S, layerTail m p) ≤ _
  rw [hsplit, ← hu2]
  calc
    _ ≤ 2 / u ^ 2 + 4 / u ^ 2 := add_le_add hsmall hlarge
    _ = 6 / u ^ 2 := by ring

end D5.S3.Arith.Robin.PriceRecord.HigherValuationTail
