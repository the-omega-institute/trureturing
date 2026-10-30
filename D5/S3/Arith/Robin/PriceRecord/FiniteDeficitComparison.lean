/- GID: D5/S3/Arith/Robin/PriceRecord/FiniteDeficitComparison
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FiniteDeficitComparison
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Exact finite Euler deficit between the actual tail and the literal prime-square record sum.
-/

import D5.S3.Arith.Robin.PriceRecord.HigherValuationTail
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import D5.S3.Arith.Robin.LogarithmBounds
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.Lattices.Klartag

/-- The literal finite square-prime correction on the actual second-layer window. -/
def finitePrimeSquareSum (m : ℕ) : ℝ :=
  ∑ p ∈ (Ioc (layerPrime m 2) (largestPrime m)).filter Nat.Prime,
    1 / (p : ℝ) ^ 2

/-- Every full positive-price predecessor record has a nonnegative finite Euler
    deficit, with an explicit bound for both the higher layers and the finite
    logarithmic excess over the literal square-prime sum. -/
theorem actual_finite_euler_deficit {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    0 ≤ tail m - finitePrimeSquareSum m ∧
      tail m - finitePrimeSquareSum m ≤
        6 / (largestPrime m : ℝ) ^ (2 / 3 : ℝ) +
          2 / (layerPrime m 2 : ℝ) ^ 3 := by
  classical
  let P := largestPrime m
  let Q := layerPrime m 2
  let S := (Ioc Q P).filter Nat.Prime
  let H := ∑ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p),
      layerTail m p
  have hm0 : 0 < m := by omega
  obtain ⟨hanti, hsupport⟩ := price_record_prime_structure hm hlambda hrecord
  have hP2 : 2 ≤ P := by
    have hne : m.primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by omega)
    obtain ⟨p, hp, hsup⟩ := exists_mem_eq_sup m.primeFactors hne id
    have hpp := Nat.prime_of_mem_primeFactors hp
    have heq : P = p := hsup
    rw [heq]
    exact hpp.two_le
  have hQ1 : 1 ≤ Q := by
    dsimp [Q, layerPrime]
    exact le_max_left _ _
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hS_eq : m.primeFactors.filter (fun p => m.factorization p = 1) = S := by
    ext p
    constructor
    · intro hp
      have hpS := mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hpS.1
      have hpP : p ≤ P := by
        rw [hsupport] at hpS
        exact (Nat.mem_primesLE.mp hpS.1).1
      have hpQ : Q < p := by
        by_contra hnot
        have hpQ' : p ≤ Q := le_of_not_gt hnot
        have hv := valuation_below_layer_prime hpp hanti hpQ'
        omega
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpQ, hpP⟩, hpp⟩
    · intro hp
      have hpS := mem_filter.mp hp
      have hpI := mem_Ioc.mp hpS.1
      have hpp := hpS.2
      have hpmem : p ∈ m.primeFactors := by
        rw [hsupport]
        exact Nat.mem_primesLE.mpr ⟨hpI.2, hpp⟩
      have hvlt := valuation_above_layer_prime hm0 (by norm_num : 1 ≤ (2 : ℕ)) hpp
        hpI.1
      have hv_eq : m.factorization p = 1 := by
        have hvpos : 1 ≤ m.factorization p :=
          hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hpmem)
        omega
      exact mem_filter.mpr ⟨hpmem, hv_eq⟩
  have htail_split : tail m = H + ∑ p ∈ S, layerTail m p := by
    rw [tail]
    have hsplit := sum_filter_add_sum_filter_not m.primeFactors
      (fun p : ℕ => 2 ≤ m.factorization p) (layerTail m)
    have hnot_eq : m.primeFactors.filter (fun p => ¬ 2 ≤ m.factorization p) =
        m.primeFactors.filter (fun p => m.factorization p = 1) := by
      ext p
      by_cases hp : p ∈ m.primeFactors
      · have hpp := Nat.prime_of_mem_primeFactors hp
        have hvpos : 1 ≤ m.factorization p :=
          hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
        simp only [mem_filter, hp, true_and]
        omega
      · simp [hp]
    dsimp [H]
    rw [← hsplit, hnot_eq, hS_eq]
  have hpoint_low (p : ℕ) (hp : p ∈ S) :
      0 ≤ layerTail m p - 1 / (p : ℝ) ^ 2 := by
    have hpp := mem_filter.mp hp |>.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hx1 : (p : ℝ)⁻¹ ^ 2 < 1 := by
      exact pow_lt_one₀ (by positivity) (by
        exact (inv_lt_one₀ hp0).mpr (by exact_mod_cast hpp.one_lt)) (by norm_num)
    have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hx1)
    have hlow : (p : ℝ)⁻¹ ^ 2 ≤ -Real.log (1 - (p : ℝ)⁻¹ ^ 2) := by
      linarith
    have hv : m.factorization p = 1 := by
      have := hS_eq ▸ hp
      exact mem_filter.mp this |>.2
    simpa [layerTail, hv, one_div, pow_two] using hlow
  have hpoint_up (p : ℕ) (hp : p ∈ S) :
      layerTail m p - 1 / (p : ℝ) ^ 2 ≤
        (Q : ℝ)⁻¹ * (1 / (p : ℝ) ^ 3) := by
    have hpp := mem_filter.mp hp |>.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hxhalf : (p : ℝ)⁻¹ ^ 2 ≤ 1 / 2 := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hi : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
        simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) hp2)
      have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ (p : ℝ)⁻¹) hi
      have hsquare' : (p : ℝ)⁻¹ ^ 2 ≤ ((2 : ℝ)⁻¹ ^ 2) := by
        simpa only [pow_two] using hsquare
      exact hsquare'.trans (by norm_num)
    have hquad := neg_log_one_sub_le (by positivity : 0 ≤ (p : ℝ)⁻¹ ^ 2) hxhalf
    have hv : m.factorization p = 1 := by
      have := hS_eq ▸ hp
      exact mem_filter.mp this |>.2
    have hexcess : layerTail m p - 1 / (p : ℝ) ^ 2 ≤
        (p : ℝ)⁻¹ ^ 4 := by
      have hraw : -Real.log (1 - (p : ℝ)⁻¹ ^ 2) - (p : ℝ)⁻¹ ^ 2 ≤
          (p : ℝ)⁻¹ ^ 4 := by
        have := (show -Real.log (1 - (p : ℝ)⁻¹ ^ 2) - (p : ℝ)⁻¹ ^ 2 ≤
            ((p : ℝ)⁻¹ ^ 2) ^ 2 by linarith [hquad])
        convert this using 1 <;> ring
      have hlayer : layerTail m p = -Real.log (1 - (p : ℝ)⁻¹ ^ 2) := by
        simp [layerTail, hv]
      have hp2eq : 1 / (p : ℝ) ^ 2 = (p : ℝ)⁻¹ ^ 2 := by
        rw [one_div, inv_pow]
      rw [hlayer, hp2eq]
      exact hraw
    have hpQ : Q < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hQp : (Q : ℝ) ≤ p := by exact_mod_cast hpQ.le
    have hinv : (p : ℝ)⁻¹ ≤ (Q : ℝ)⁻¹ := by
      simpa only [one_div] using (one_div_le_one_div_of_le hQ0 hQp)
    have hpow := mul_le_mul_of_nonneg_right hinv (by positivity : 0 ≤ (p : ℝ)⁻¹ ^ 3)
    have hp3eq : 1 / (p : ℝ) ^ 3 = (p : ℝ)⁻¹ ^ 3 := by
      rw [one_div, inv_pow]
    have hpow' : (p : ℝ)⁻¹ * (1 / (p : ℝ) ^ 3) ≤
        (Q : ℝ)⁻¹ * (1 / (p : ℝ) ^ 3) := by
      rw [hp3eq]
      exact hpow
    calc
      _ ≤ (p : ℝ)⁻¹ ^ 4 := hexcess
      _ = (p : ℝ)⁻¹ * (1 / (p : ℝ) ^ 3) := by
        rw [show 1 / (p : ℝ) ^ 3 = (p : ℝ)⁻¹ ^ 3 by
          rw [one_div, inv_pow]]
        ring
      _ ≤ (Q : ℝ)⁻¹ * (1 / (p : ℝ) ^ 3) := hpow'
  have hE_low : 0 ≤ ∑ p ∈ S, (layerTail m p - 1 / (p : ℝ) ^ 2) :=
    sum_nonneg (fun p hp => hpoint_low p hp)
  have hE_up : (∑ p ∈ S, (layerTail m p - 1 / (p : ℝ) ^ 2)) ≤
      2 / (Q : ℝ) ^ 3 := by
    calc
      _ ≤ ∑ p ∈ S, (Q : ℝ)⁻¹ * (1 / (p : ℝ) ^ 3) :=
        sum_le_sum (fun p hp => hpoint_up p hp)
      _ = (Q : ℝ)⁻¹ * ∑ p ∈ S, 1 / (p : ℝ) ^ 3 := by
        rw [Finset.mul_sum]
      _ ≤ (Q : ℝ)⁻¹ * (2 / (Q : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply finite_cubic_tail hQ0
        intro p hp
        exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).1
      _ = 2 / (Q : ℝ) ^ 3 := by
        field_simp
  have hE_id : tail m - finitePrimeSquareSum m = H +
      ∑ p ∈ S, (layerTail m p - 1 / (p : ℝ) ^ 2) := by
    rw [htail_split]
    dsimp [finitePrimeSquareSum, S]
    rw [sum_sub_distrib]
    ring
  have hH : H ≤ 6 / (P : ℝ) ^ (2 / 3 : ℝ) := by
    simpa [H, P] using
      (D5.S3.Arith.Robin.PriceRecord.HigherValuationTail.higher_valuation_tail
        hm hlambda hrecord)
  have hnonneg : 0 ≤ tail m - finitePrimeSquareSum m := by
    rw [hE_id]
    exact add_nonneg (sum_nonneg (fun p hp => layer_tail_nonneg m
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1))) hE_low
  have hupper : tail m - finitePrimeSquareSum m ≤
      6 / (P : ℝ) ^ (2 / 3 : ℝ) + 2 / (Q : ℝ) ^ 3 := by
    rw [hE_id]
    exact add_le_add hH hE_up
  simpa [P, Q] using And.intro hnonneg hupper

end D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison
