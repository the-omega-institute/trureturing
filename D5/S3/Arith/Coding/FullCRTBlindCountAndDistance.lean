/- GID: D5/S3/Arith/Coding/FullCRTBlindCountAndDistance
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/FullCRTBlindCountAndDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full CRT range has maximal blind count one below its length and distance one. -/

import D5.S3.Arith.Coding.FullCRTDynamicRangeNoCorrectionMargin
import Mathlib.Tactic

/- Library-search audit trail (2026-08-26):
   * Current-tree name and body-shape searches for `maximumBlindCoordinateCount`,
     powerset products, `residueMinimumDistance`, and distance-one witnesses found
     the family SSOT in `ExactResidueCodeMinimumDistance` and the frozen full-range
     distance theorem in `FullCRTDynamicRangeNoCorrectionMargin`.
   * The frozen full-range theorem explicitly omits the maximal-blind-count clause,
     so it is imported for the distance clause rather than wrapped as complete coverage.
   * Pinned Mathlib searches found `Finset.le_sup`, `Finset.card_map`,
     `Fin.prod_univ_castSucc`, and `Nat.sInf_mem`; these supply the attained
     `n - 1` coordinate subset and the explicit distance-one codeword pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.FullCRTBlindCountAndDistance

open D5.S3.Arith.Coding.ResidueCodeDynamicRange
open D5.S3.Arith.Coding.ExactResidueCodeMinimumDistance
open D5.S3.Arith.Coding.FullCRTDynamicRangeNoCorrectionMargin

/-- For a nonempty strictly increasing pairwise-coprime modulus family above one,
using the full product makes exactly `n - 1` coordinates simultaneously blind and
gives exact minimum distance one. The residue word remains injective on the full
message range, but an explicit pair of valid words differs in only one coordinate. -/
theorem full_crt_blind_count_distance_and_detection_limit
    (m : ℕ → ℕ) (n : ℕ)
    (hn : 0 < n)
    (hstrict : ∀ i j, i < j → j < n → m i < m j)
    (hmodulus : ∀ i, i < n → 2 ≤ m i)
    (hcoprime : ∀ i j, i < n → j < n → i ≠ j → Nat.Coprime (m i) (m j)) :
    maximumBlindCoordinateCount m n (prefixProduct m n) = n - 1 ∧
      residueMinimumDistance m n (prefixProduct m n) = 1 ∧
      (∀ x y, x < prefixProduct m n → y < prefixProduct m n →
        residueWord m n x = residueWord m n y → x = y) ∧
      ∃ x y, x < y ∧ y < prefixProduct m n ∧
        hammingDist (residueWord m n x) (residueWord m n y) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hmonotone : ∀ i j, i ≤ j → j < k + 1 → m i ≤ m j := by
    intro i j hij hj
    rcases hij.eq_or_lt with (rfl | hij)
    · exact le_rfl
    · exact (hstrict i j hij hj).le
  have hmodulusOne : ∀ i, i < k + 1 → 1 < m i := by
    intro i hi
    exact lt_of_lt_of_le Nat.one_lt_two (hmodulus i hi)
  have hpositive : ∀ i, i < k + 1 → 0 < m i := by
    intro i hi
    exact (hmodulusOne i hi).trans' Nat.zero_lt_one
  have hprefixPositive : 0 < prefixProduct m k := by
    simp only [prefixProduct]
    apply Finset.prod_pos
    intro i _
    exact hpositive i (by omega)
  have hlast : 2 ≤ m k := hmodulus k (by omega)
  have hfull : prefixProduct m (k + 1) = prefixProduct m k * m k := by
    simp [prefixProduct, Fin.prod_univ_castSucc]
  have hprefixLtFull : prefixProduct m k < prefixProduct m (k + 1) := by
    rw [hfull]
    exact lt_mul_of_one_lt_right hprefixPositive (hmodulusOne k (by omega))
  have hfullAtLeastTwo : 2 ≤ prefixProduct m (k + 1) := by
    rw [hfull]
    have hprefixAtLeastOne : 1 ≤ prefixProduct m k := by omega
    simpa using Nat.mul_le_mul hprefixAtLeastOne hlast
  let prefixEmbedding : Fin k ↪ Fin (k + 1) := Fin.castLEEmb (Nat.le_succ k)
  let prefixCoordinates : Finset (Fin (k + 1)) := Finset.univ.map prefixEmbedding
  have hprefixProduct :
      (∏ i ∈ prefixCoordinates, m (i : ℕ)) = prefixProduct m k := by
    simp only [prefixCoordinates, prefixProduct, Finset.prod_map]
    rfl
  have hprefixCandidate :
      prefixCoordinates ∈
        ((Finset.univ : Finset (Fin (k + 1))).powerset.filter
          fun coordinates : Finset (Fin (k + 1)) =>
            (∏ i ∈ coordinates, m (i : ℕ)) < prefixProduct m (k + 1)) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    rw [hprefixProduct]
    exact hprefixLtFull
  have hblindLower :
      k ≤ maximumBlindCoordinateCount m (k + 1) (prefixProduct m (k + 1)) := by
    rw [maximumBlindCoordinateCount]
    have hcardLe := Finset.le_sup hprefixCandidate (f := Finset.card)
    simpa only [prefixCoordinates, Finset.card_map, Finset.card_univ,
      Fintype.card_fin] using hcardLe
  have hblindLe :
      maximumBlindCoordinateCount m (k + 1) (prefixProduct m (k + 1)) ≤ k + 1 := by
    rw [maximumBlindCoordinateCount]
    apply Finset.sup_le
    intro coordinates hcoordinates
    have hsubset := Finset.mem_powerset.mp (Finset.mem_filter.mp hcoordinates).1
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsubset
  have hblindNe :
      maximumBlindCoordinateCount m (k + 1) (prefixProduct m (k + 1)) ≠ k + 1 := by
    intro hblind
    have hbounds := maximumBlindCoordinateCount_prefix_bounds
      m (k + 1) (prefixProduct m (k + 1)) hfullAtLeastTwo (le_refl _) hmonotone
    rw [hblind] at hbounds
    exact (Nat.lt_irrefl _) hbounds.1
  have hblind :
      maximumBlindCoordinateCount m (k + 1) (prefixProduct m (k + 1)) = k := by
    omega
  have hminimum :
      residueMinimumDistance m (k + 1) (prefixProduct m (k + 1)) = 1 :=
    full_crt_dynamic_range_minimum_distance m (k + 1) (by omega)
      hmonotone hmodulusOne hcoprime
  have hminimumOne :
      MinDistanceAtLeast m (k + 1) (prefixProduct m (k + 1)) 1 :=
    (minDistanceAtLeast_iff_le_residueMinimumDistance m (k + 1)
      (prefixProduct m (k + 1)) 1 hfullAtLeastTwo).mpr (by omega)
  have hinjective :
      ∀ x y, x < prefixProduct m (k + 1) → y < prefixProduct m (k + 1) →
        residueWord m (k + 1) x = residueWord m (k + 1) y → x = y := by
    intro x y hx hy hwords
    by_cases hxy : x < y
    · have hone := hminimumOne x y hxy hy
      rw [hwords, hammingDist_self] at hone
      omega
    · by_cases heq : x = y
      · exact heq
      · have hyx : y < x := by omega
        have hone := hminimumOne y x hyx hx
        rw [← hwords, hammingDist_self] at hone
        omega
  have hdistanceSetNonempty :
      ({distance : ℕ | ∃ x y, x < y ∧ y < prefixProduct m (k + 1) ∧
        hammingDist (residueWord m (k + 1) x) (residueWord m (k + 1) y) =
          distance} : Set ℕ).Nonempty := by
    exact ⟨hammingDist (residueWord m (k + 1) 0) (residueWord m (k + 1) 1),
      0, 1, by omega, by omega, rfl⟩
  have hattained := Nat.sInf_mem hdistanceSetNonempty
  change ∃ x y, x < y ∧ y < prefixProduct m (k + 1) ∧
    hammingDist (residueWord m (k + 1) x) (residueWord m (k + 1) y) =
      residueMinimumDistance m (k + 1) (prefixProduct m (k + 1)) at hattained
  rw [hminimum] at hattained
  simpa only [Nat.add_sub_cancel] using ⟨hblind, hminimum, hinjective, hattained⟩

#print axioms full_crt_blind_count_distance_and_detection_limit

end D5.S3.Arith.Coding.FullCRTBlindCountAndDistance
