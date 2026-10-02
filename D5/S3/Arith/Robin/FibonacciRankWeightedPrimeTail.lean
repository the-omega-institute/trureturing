/- GID: D5/S3/Arith/Robin/FibonacciRankWeightedPrimeTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/FibonacciRankWeightedPrimeTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Weighted prime Fibonacci first-rank tails have an explicit summable bound. -/

import D5.S3.Arith.Robin.FibonacciRankEulerTail
import D5.S3.Arith.FibonacciAtomic.TimeSampling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace D5.S3.Arith.Robin.FibonacciRankWeightedPrimeTail

open Finset
open D5.S3.Arith.Robin.FibonacciRankEulerTail
open D5.S3.Arith.FibonacciAtomic.TimeSampling

/-- The prime first-rank weight above a real cutoff. -/
noncomputable def weight (y : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ y < (p : ℝ) then 1 / ((p : ℝ) * (zeroRank p : ℝ)) else 0

/-- The actual least-positive Fibonacci zero rank gives a summable prime tail. -/
theorem result (y : ℝ) (hy : 2 ≤ y) :
    Summable (weight y) ∧ ∑' p : ℕ, weight y p ≤ 16 / Real.sqrt y := by
  classical
  have hy0 : 0 < y := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hbuck (d p : ℕ) : p ∈ rankBucket d ↔ p.Prime ∧ zeroRank p = d := by
    constructor
    · intro hp
      have h := hp
      simp only [rankBucket, Finset.mem_filter] at h
      have hpp := Nat.prime_of_mem_primeFactors h.1
      have hz := prime_zero_rank_facts p hpp
      have hd0 : 0 < d := Nat.fib_pos.mp
        (Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp h.1).2.2)
      exact ⟨hpp, Nat.le_antisymm
        (hz.2.2 d hd0 (Nat.dvd_of_mem_primeFactors h.1))
        (rank_bucket_min d p hp (zeroRank p) hz.1 hz.2.1)⟩
    · rintro ⟨hpp, heq⟩
      have hz := prime_zero_rank_facts p hpp
      rw [heq] at hz
      simp only [rankBucket, Finset.mem_filter]
      refine ⟨Nat.mem_primeFactors.mpr ⟨hpp, hz.2.1, (Nat.fib_pos.mpr hz.1).ne'⟩, ?_⟩
      intro k hk hpk
      have hmin := hz.2.2 k (by have := (Finset.mem_Ico.mp hk).1; omega) hpk
      have hlt := (Finset.mem_Ico.mp hk).2
      omega
  have hcardall := rank_bucket_card_lt
  have hshell (Y : ℝ) (hY : 2 ≤ Y) (s : Finset ℕ)
      (hs : ∀ p ∈ s, p.Prime ∧ Y ≤ (p : ℝ) ∧ (p : ℝ) < 2 * Y) :
      (∑ p ∈ s, 1 / ((p : ℝ) * (zeroRank p : ℝ))) ≤ 3 / Real.sqrt Y := by
    have hY0 : 0 < Y := by linarith
    have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
    have hsquare := Real.sq_sqrt hY0.le
    let small := s.filter fun p => (zeroRank p : ℝ) ≤ Real.sqrt Y
    let large := s.filter fun p => ¬ (zeroRank p : ℝ) ≤ Real.sqrt Y
    have hsmallmap (p : ℕ) (hp : p ∈ small) :
        zeroRank p ∈ Finset.Icc 1 ⌊Real.sqrt Y⌋₊ := by
      have hpS := (Finset.mem_filter.mp hp).1
      have hz := (prime_zero_rank_facts p (hs p hpS).1).1
      exact Finset.mem_Icc.mpr ⟨hz, Nat.le_floor (Finset.mem_filter.mp hp).2⟩
    have hsmallbound : (∑ p ∈ small, 1 / ((p : ℝ) * (zeroRank p : ℝ))) ≤
        1 / Real.sqrt Y := by
      rw [← Finset.sum_fiberwise_of_maps_to hsmallmap]
      have hpart (d : ℕ) (hd : d ∈ Finset.Icc 1 ⌊Real.sqrt Y⌋₊) :
          (∑ p ∈ small.filter (fun p => zeroRank p = d),
            1 / ((p : ℝ) * (zeroRank p : ℝ))) ≤ 1 / Y := by
        have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
        have hsub : small.filter (fun p => zeroRank p = d) ⊆ rankBucket d := by
          intro p hp
          obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
          exact (hbuck d p).mpr ⟨(hs p (Finset.mem_filter.mp hp).1).1, heq⟩
        have hcard : ((small.filter (fun p => zeroRank p = d)).card : ℝ) ≤ d := by
          exact_mod_cast (Finset.card_le_card hsub).trans (hcardall d hd0).le
        calc
          _ ≤ ∑ _p ∈ small.filter (fun p => zeroRank p = d), 1 / (Y * (d : ℝ)) := by
            apply Finset.sum_le_sum
            intro p hp
            obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
            rw [heq]
            apply one_div_le_one_div_of_le (mul_pos hY0 hdR)
            exact mul_le_mul_of_nonneg_right (hs p (Finset.mem_filter.mp hp).1).2.1 hdR.le
          _ = ((small.filter (fun p => zeroRank p = d)).card : ℝ) / (Y * (d : ℝ)) := by
            simp [div_eq_mul_inv]
          _ ≤ (d : ℝ) / (Y * (d : ℝ)) :=
            div_le_div_of_nonneg_right hcard (mul_pos hY0 hdR).le
          _ = 1 / Y := by field_simp
      calc
        _ ≤ ∑ _d ∈ Finset.Icc 1 ⌊Real.sqrt Y⌋₊, 1 / Y := Finset.sum_le_sum hpart
        _ = (⌊Real.sqrt Y⌋₊ : ℝ) / Y := by simp [Nat.card_Icc, div_eq_mul_inv]
        _ ≤ Real.sqrt Y / Y := div_le_div_of_nonneg_right
          (Nat.floor_le (Real.sqrt_nonneg Y)) hY0.le
        _ = 1 / Real.sqrt Y := by apply (div_eq_div_iff hY0.ne' hsY.ne').mpr; nlinarith
    have hlargecard : (large.card : ℝ) ≤ 2 * Y := by
      have hsub : large ⊆ Finset.Icc 1 ⌊2 * Y⌋₊ := by
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have h := hs p hpS
        exact Finset.mem_Icc.mpr ⟨h.1.one_le, Nat.le_floor h.2.2.le⟩
      have hcard : large.card ≤ ⌊2 * Y⌋₊ := by
        simpa [Nat.card_Icc] using Finset.card_le_card hsub
      exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (by positivity))
    have hlargebound : (∑ p ∈ large, 1 / ((p : ℝ) * (zeroRank p : ℝ))) ≤
        2 / Real.sqrt Y := by
      have hterm (p : ℕ) (hp : p ∈ large) :
          1 / ((p : ℝ) * (zeroRank p : ℝ)) ≤ 1 / (Y * Real.sqrt Y) := by
        obtain ⟨hpS, hpL⟩ := Finset.mem_filter.mp hp
        apply one_div_le_one_div_of_le (mul_pos hY0 hsY)
        apply mul_le_mul (hs p hpS).2.1 (le_of_lt (lt_of_not_ge hpL)) hsY.le
        exact (hY0.trans_le (hs p hpS).2.1).le
      calc
        _ ≤ ∑ _p ∈ large, 1 / (Y * Real.sqrt Y) := Finset.sum_le_sum hterm
        _ = (large.card : ℝ) / (Y * Real.sqrt Y) := by simp [div_eq_mul_inv]
        _ ≤ (2 * Y) / (Y * Real.sqrt Y) :=
          div_le_div_of_nonneg_right hlargecard (mul_pos hY0 hsY).le
        _ = 2 / Real.sqrt Y := by field_simp
    have hsplit := Finset.sum_filter_add_sum_filter_not s
      (fun p => (zeroRank p : ℝ) ≤ Real.sqrt Y)
      (fun p => 1 / ((p : ℝ) * (zeroRank p : ℝ)))
    change (∑ p ∈ small, _) + (∑ p ∈ large, _) = _ at hsplit
    rw [← hsplit]
    calc
      _ ≤ 1 / Real.sqrt Y + 2 / Real.sqrt Y := add_le_add hsmallbound hlargebound
      _ = _ := by ring
  let q := (Real.sqrt 2)⁻¹
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqle : q ≤ 3 / 4 := by
    have hroot : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have hroot0 : (0 : ℝ) < Real.sqrt 2 := by positivity
    dsimp [q]
    rw [← one_div]
    apply (div_le_iff₀ hroot0).mpr
    nlinarith
  have hq1 : q < 1 := by linarith
  have hgeom : Summable (fun k : ℕ => (3 / Real.sqrt y) * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsumgeom : (∑' k : ℕ, (3 / Real.sqrt y) * q ^ k) ≤ 16 / Real.sqrt y := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    have hinv : (1 - q)⁻¹ ≤ 4 := by
      rw [← one_div]
      apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
      linarith
    calc
      _ ≤ (3 / Real.sqrt y) * 4 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ 16 / Real.sqrt y := by
        rw [show (3 / Real.sqrt y) * 4 = 12 / Real.sqrt y by ring]
        exact div_le_div_of_nonneg_right (by norm_num) hsy.le
  have huniform (s : Finset ℕ) : (∑ p ∈ s, weight y p) ≤ 16 / Real.sqrt y := by
    let S : Finset ℕ := s.filter fun p : ℕ => p.Prime ∧ y < (p : ℝ)
    have hnear (p : ℕ) : ∃ k : ℕ, p ∈ S →
        y * (2 : ℝ) ^ k ≤ p ∧ (p : ℝ) < y * 2 ^ (k + 1) := by
      by_cases hp : p ∈ S
      · have hpy := (Finset.mem_filter.mp hp).2.2
        obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near
          (show (1 : ℝ) ≤ (p : ℝ) / y from (le_div_iff₀ hy0).mpr (by linarith))
          (by norm_num : (1 : ℝ) < 2)
        refine ⟨k, fun _ => ⟨?_, ?_⟩⟩
        · nlinarith [(le_div_iff₀ hy0).mp hklo]
        · nlinarith [(div_lt_iff₀ hy0).mp hkhi]
      · exact ⟨0, fun h => False.elim (hp h)⟩
    choose k hk using hnear
    have hsplit : (∑ p ∈ S, 1 / ((p : ℝ) * (zeroRank p : ℝ))) =
        ∑ j ∈ S.image k, ∑ p ∈ S.filter (fun p => k p = j),
          1 / ((p : ℝ) * (zeroRank p : ℝ)) :=
      (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem k hp) _).symm
    have hshells (j : ℕ) (hj : j ∈ S.image k) :
        (∑ p ∈ S.filter (fun p => k p = j), 1 / ((p : ℝ) * (zeroRank p : ℝ))) ≤
          (3 / Real.sqrt y) * q ^ j := by
      have hpw : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hY : 2 ≤ y * (2 : ℝ) ^ j := by nlinarith
      have hbound := hshell (y * 2 ^ j) hY (S.filter fun p => k p = j) (by
        intro p hp
        obtain ⟨hpS, heq⟩ := Finset.mem_filter.mp hp
        have h := hk p hpS
        rw [heq] at h
        refine ⟨(Finset.mem_filter.mp hpS).2.1, h.1, ?_⟩
        simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h.2)
      apply hbound.trans_eq
      rw [Real.sqrt_mul hy0.le]
      have hpowsqrt : Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
        simpa [NNReal.sqrtHom]
          using congrArg NNReal.toReal (map_pow NNReal.sqrtHom (2 : NNReal) j)
      rw [hpowsqrt]
      dsimp [q]
      rw [inv_pow]
      ring
    calc
      _ = ∑ p ∈ S, 1 / ((p : ℝ) * (zeroRank p : ℝ)) := by
        simp only [S, weight, Finset.sum_filter]
      _ = _ := hsplit
      _ ≤ ∑ j ∈ S.image k, (3 / Real.sqrt y) * q ^ j := Finset.sum_le_sum hshells
      _ ≤ ∑' j : ℕ, (3 / Real.sqrt y) * q ^ j :=
        hgeom.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ _ := hsumgeom
  have hnonneg : 0 ≤ weight y := by
    intro p
    dsimp [weight]
    split_ifs <;> positivity
  exact ⟨summable_of_sum_le hnonneg huniform, Real.tsum_le_of_sum_le hnonneg huniform⟩


end D5.S3.Arith.Robin.FibonacciRankWeightedPrimeTail
