/- GID: D5/S3/Arith/Density/TotientWeightCrowding
   generality: G
   mirror-B: D5/B/S3/Arith/Density/TotientWeightCrowding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Totient, mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Cubed finite positive support size is bounded by sixteen times squared totient weight. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Arith.Density.TotientWeightCrowding

open scoped BigOperators

/-- The total Euler totient weight controls the size of any finite positive support. -/
theorem finite_totient_weight_crowding (A : Finset ℕ) (hA : ∀ d ∈ A, 0 < d) :
    A.card ^ 3 ≤ 16 * (∑ d ∈ A, Nat.totient d) ^ 2 := by
  classical
  have hpoint : ∀ n : ℕ, 0 < n → n ≤ 2 * (Nat.totient n) ^ 2 := by
    intro n hn
    have hoddprod : (∏ p ∈ n.primeFactors.erase 2, p) ≤
        (∏ p ∈ n.primeFactors.erase 2, (p - 1)) ^ 2 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_le_prod'
      intro p hp
      obtain ⟨hp2, hp⟩ := Finset.mem_erase.mp hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hpge : 3 ≤ p := by have := hpprime.two_le; omega
      have hsub : p - 1 + 1 = p := by omega
      nlinarith
    have hradical : (∏ p ∈ n.primeFactors, p) ≤
        2 * (∏ p ∈ n.primeFactors, (p - 1)) ^ 2 := by
      by_cases htwo : 2 ∈ n.primeFactors
      · have hr := Finset.prod_erase_mul n.primeFactors (fun p => p) htwo
        have ht := Finset.prod_erase_mul n.primeFactors (fun p => p - 1) htwo
        norm_num at ht
        rw [← hr, ← ht]
        nlinarith [hoddprod]
      · rw [Finset.erase_eq_self.mpr htwo] at hoddprod
        omega
    let q := n / ∏ p ∈ n.primeFactors, p
    have hnq : q * (∏ p ∈ n.primeFactors, p) = n :=
      Nat.div_mul_cancel (Nat.prod_primeFactors_dvd n)
    have hq : 1 ≤ q := by
      apply Nat.pos_of_ne_zero
      intro hq0
      rw [hq0, zero_mul] at hnq
      omega
    rw [Nat.totient_eq_div_primeFactors_mul]
    change n ≤ 2 * (q * (∏ p ∈ n.primeFactors, (p - 1))) ^ 2
    calc
      n = q * (∏ p ∈ n.primeFactors, p) := hnq.symm
      _ ≤ q * (2 * (∏ p ∈ n.primeFactors, (p - 1)) ^ 2) :=
        Nat.mul_le_mul_left q hradical
      _ ≤ 2 * (q * (∏ p ∈ n.primeFactors, (p - 1))) ^ 2 := by
        have hqSq : q ≤ q ^ 2 := by nlinarith [Nat.mul_le_mul_right q hq]
        have hmul := Nat.mul_le_mul_right
          (2 * (∏ p ∈ n.primeFactors, (p - 1)) ^ 2) hqSq
        nlinarith
  by_cases hk0 : A.card = 0
  · simp [hk0]
  let low := A.filter (fun d => 4 * (Nat.totient d) ^ 2 ≤ A.card)
  let high := A \ low
  have hlowA : low ⊆ A := Finset.filter_subset _ _
  have hlow : low ⊆ Finset.Icc 1 (A.card / 2) := by
    intro d hd
    obtain ⟨hdA, hdφ⟩ := Finset.mem_filter.mp hd
    have hdpos := hA d hdA
    have hdpoint := hpoint d hdpos
    have hd2 : 2 * d ≤ A.card := by nlinarith
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hlowcard : low.card ≤ A.card / 2 := by
    have hc := Finset.card_le_card hlow
    simpa using hc
  have hpartition : high.card + low.card = A.card :=
    Finset.card_sdiff_add_card_eq_card hlowA
  have hhighcard : A.card ≤ 2 * high.card := by omega
  have hhigh : high.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image high Nat.totient hhigh
  have hthreshold : A.card < 4 * (Nat.totient d) ^ 2 := by
    obtain ⟨hdA, hdnot⟩ := Finset.mem_sdiff.mp hd
    have : ¬4 * (Nat.totient d) ^ 2 ≤ A.card := by
      intro h
      exact hdnot (Finset.mem_filter.mpr ⟨hdA, h⟩)
    omega
  have hweight : high.card * Nat.totient d ≤ ∑ e ∈ A, Nat.totient e := by
    calc
      high.card * Nat.totient d = ∑ e ∈ high, Nat.totient d := by simp
      _ ≤ ∑ e ∈ high, Nat.totient e := Finset.sum_le_sum hmin
      _ ≤ ∑ e ∈ A, Nat.totient e :=
        Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have hcardSq : A.card ^ 2 ≤ 4 * high.card ^ 2 := by nlinarith
  have hfirst := Nat.mul_le_mul_right A.card hcardSq
  have hsecond := Nat.mul_le_mul_left (4 * high.card ^ 2) (Nat.le_of_lt hthreshold)
  have hlast : (high.card * Nat.totient d) ^ 2 ≤ (∑ e ∈ A, Nat.totient e) ^ 2 := by
    exact Nat.pow_le_pow_left hweight 2
  calc
    A.card ^ 3 = A.card ^ 2 * A.card := by ring
    _ ≤ 4 * high.card ^ 2 * A.card := hfirst
    _ ≤ 4 * high.card ^ 2 * (4 * (Nat.totient d) ^ 2) := hsecond
    _ = 16 * (high.card * Nat.totient d) ^ 2 := by ring
    _ ≤ 16 * (∑ e ∈ A, Nat.totient e) ^ 2 := Nat.mul_le_mul_left 16 hlast

end D5.S3.Arith.Density.TotientWeightCrowding
