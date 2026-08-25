/- GID: D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full CRT range has distance one; zero length, units, and short ranges are audited. -/

import D5.S3.Arith.Coding.ExactResidueCodeMinimumDistance
import D5.S3.Arith.Coding.ResidueCodeDynamicRange
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Current-tree searches for the source symbol `t`, an error-correction count, and
     full-range CRT distance found no definition of `t` with the asserted meaning.
   * `ResidueCodeDynamicRange` is the family SSOT for `residueWord`,
     `MinDistanceAtLeast`, `prefixProduct`, and
     `maximum_dynamic_range_iff_min_distance`; the proof below applies that theorem
     at distances one, two, and `n` rather than reproving its CRT argument.
   * `ExactResidueCodeMinimumDistance` supplies the named `residueMinimumDistance`
     object and `minDistanceAtLeast_iff_le_residueMinimumDistance`.
   * Pinned Mathlib searches found `Fin.prod_univ_castSucc`, `Nat.sInf_le`, and
     `hammingDist_le_card_fintype` for the final-factor and boundary calculations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.FullCRTDynamicRangeNoCorrectionMargin

open D5.S3.Arith.Coding.ExactResidueCodeMinimumDistance
open D5.S3.Arith.Coding.ResidueCodeDynamicRange

/- The source's clause `t(K) = n - 1` is not covered: no definition of `t` with this
meaning exists in the volume, and the standard correction radius would instead be zero. -/

/-- At the maximum possible distance `d = n`, the dynamic range is bounded by the
first modulus alone. -/
theorem maximum_possible_distance_iff_first_modulus_bound (m : ℕ → ℕ) (n K : ℕ)
    (hn : 0 < n)
    (hmonotone : ∀ i j, i ≤ j → j < n → m i ≤ m j)
    (hpositive : ∀ i, i < n → 0 < m i)
    (hcoprime : ∀ i j, i < n → j < n → i ≠ j → Nat.Coprime (m i) (m j)) :
    MinDistanceAtLeast m n K n ↔ K ≤ prefixProduct m 1 := by
  have hindex : n - n + 1 = 1 := by omega
  simpa only [hindex] using
    (maximum_dynamic_range_iff_min_distance m n n K (by omega) (le_refl n)
      hmonotone hpositive hcoprime)
#print axioms maximum_possible_distance_iff_first_modulus_bound

/-- For a nonempty ordered pairwise-coprime modulus family with every modulus above
one, using the entire CRT product gives exact minimum Hamming distance one. The strict
modulus bound is essential because the last-factor growth rules out distance two. -/
theorem full_crt_dynamic_range_minimum_distance (m : ℕ → ℕ) (n : ℕ)
    (hn : 0 < n)
    (hmonotone : ∀ i j, i ≤ j → j < n → m i ≤ m j)
    (hmodulus : ∀ i, i < n → 1 < m i)
    (hcoprime : ∀ i j, i < n → j < n → i ≠ j → Nat.Coprime (m i) (m j)) :
    residueMinimumDistance m n (prefixProduct m n) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hpositive : ∀ i, i < k + 1 → 0 < m i := by
    intro i hi
    exact (hmodulus i hi).trans' Nat.zero_lt_one
  have hprefixPositive : 0 < prefixProduct m k := by
    simp only [prefixProduct]
    apply Finset.prod_pos
    intro i _
    exact hpositive i (by omega)
  have hlast : 2 ≤ m k := by
    have := hmodulus k (by omega)
    omega
  have hfull : prefixProduct m (k + 1) = prefixProduct m k * m k := by
    simp [prefixProduct, Fin.prod_univ_castSucc]
  have hfullAtLeastTwo : 2 ≤ prefixProduct m (k + 1) := by
    rw [hfull]
    have hprefixAtLeastOne : 1 ≤ prefixProduct m k := by omega
    simpa using Nat.mul_le_mul hprefixAtLeastOne hlast
  have hminimumOne : MinDistanceAtLeast m (k + 1) (prefixProduct m (k + 1)) 1 := by
    apply (maximum_dynamic_range_iff_min_distance m (k + 1) 1
      (prefixProduct m (k + 1)) (by omega) (by omega)
      hmonotone hpositive hcoprime).mpr
    have hindex : k + 1 - 1 + 1 = k + 1 := by omega
    rw [hindex]
  have hlower : 1 ≤ residueMinimumDistance m (k + 1) (prefixProduct m (k + 1)) :=
    (minDistanceAtLeast_iff_le_residueMinimumDistance m (k + 1)
      (prefixProduct m (k + 1)) 1 hfullAtLeastTwo).mp hminimumOne
  by_cases hk : k = 0
  · subst k
    have honeLtFull : 1 < prefixProduct m 1 := by
      have : 2 ≤ prefixProduct m 1 := by simpa using hfullAtLeastTwo
      omega
    have hwitness :
        hammingDist (residueWord m 1 0) (residueWord m 1 1) ∈
          {distance : ℕ | ∃ x y, x < y ∧ y < prefixProduct m 1 ∧
            hammingDist (residueWord m 1 x) (residueWord m 1 y) = distance} := by
      exact ⟨0, 1, by omega, honeLtFull, rfl⟩
    have hminimumLe :
        residueMinimumDistance m 1 (prefixProduct m 1) ≤
          hammingDist (residueWord m 1 0) (residueWord m 1 1) := by
      unfold residueMinimumDistance
      exact Nat.sInf_le hwitness
    have hdistanceLe :
        hammingDist (residueWord m 1 0) (residueWord m 1 1) ≤ 1 := by
      simpa only [Fintype.card_fin] using
        (hammingDist_le_card_fintype :
          hammingDist (residueWord m 1 0) (residueWord m 1 1) ≤ Fintype.card (Fin 1))
    exact Nat.le_antisymm (hminimumLe.trans hdistanceLe) hlower
  · have hkpositive : 0 < k := Nat.pos_of_ne_zero hk
    have hprefixLtFull : prefixProduct m k < prefixProduct m (k + 1) := by
      rw [hfull]
      exact lt_mul_of_one_lt_right hprefixPositive (hmodulus k (by omega))
    have hnotMinimumTwo :
        ¬MinDistanceAtLeast m (k + 1) (prefixProduct m (k + 1)) 2 := by
      intro hminimumTwo
      have hbound :=
        (maximum_dynamic_range_iff_min_distance m (k + 1) 2
          (prefixProduct m (k + 1)) (by omega) (by omega)
          hmonotone hpositive hcoprime).mp hminimumTwo
      have hindex : k + 1 - 2 + 1 = k := by omega
      rw [hindex] at hbound
      exact (Nat.not_le_of_gt hprefixLtFull) hbound
    have hnotTwo :
        ¬2 ≤ residueMinimumDistance m (k + 1) (prefixProduct m (k + 1)) := by
      intro htwo
      apply hnotMinimumTwo
      exact (minDistanceAtLeast_iff_le_residueMinimumDistance m (k + 1)
        (prefixProduct m (k + 1)) 2 hfullAtLeastTwo).mpr htwo
    have hupper :
        residueMinimumDistance m (k + 1) (prefixProduct m (k + 1)) ≤ 1 :=
      Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hnotTwo)
    exact Nat.le_antisymm hupper hlower
#print axioms full_crt_dynamic_range_minimum_distance

/-- Positive code length is necessary: at `n = 0`, the indexed modulus assumptions
are vacuous, the full prefix product is one, and the minimum-distance set is empty. -/
theorem positive_length_is_necessary :
    residueMinimumDistance (fun _ : ℕ => 2) 0
      (prefixProduct (fun _ : ℕ => 2) 0) = 0 := by
  simp [residueMinimumDistance, prefixProduct, Nat.sInf_empty]
#print axioms positive_length_is_necessary

/-- The modulus-above-one hypothesis is necessary: a single unit modulus has full
product one and hence no pair of distinct messages in its full message range. -/
theorem modulus_greater_than_one_is_necessary :
    residueMinimumDistance (fun _ : ℕ => 1) 1
      (prefixProduct (fun _ : ℕ => 1) 1) = 0 := by
  simp [residueMinimumDistance, prefixProduct, Nat.sInf_empty]
#print axioms modulus_greater_than_one_is_necessary

/-- Pairwise coprimality is necessary: moduli two and four meet the ordering and
strict size conditions, but messages zero and four have identical full residue words. -/
theorem pairwise_coprime_is_necessary :
    ∃ m : ℕ → ℕ,
      (∀ i, i < 2 → 1 < m i) ∧
      (∀ i j, i ≤ j → j < 2 → m i ≤ m j) ∧
      ¬Nat.Coprime (m 0) (m 1) ∧
      residueMinimumDistance m 2 (prefixProduct m 2) = 0 := by
  let m : ℕ → ℕ := fun i => if i = 0 then 2 else 4
  refine ⟨m, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [m]
    split <;> omega
  · intro i j hij hj
    simp only [m]
    split <;> split <;> omega
  · norm_num [m]
  · have hfull : prefixProduct m 2 = 8 := by decide
    have hsame : residueWord m 2 0 = residueWord m 2 4 := by
      funext i
      fin_cases i <;> decide
    have hnotMinimumOne : ¬MinDistanceAtLeast m 2 (prefixProduct m 2) 1 := by
      intro hminimumOne
      have hbound := hminimumOne 0 4 (by omega) (by omega)
      rw [hsame, hammingDist_self] at hbound
      omega
    have hnotOne : ¬1 ≤ residueMinimumDistance m 2 (prefixProduct m 2) := by
      intro hone
      apply hnotMinimumOne
      apply (minDistanceAtLeast_iff_le_residueMinimumDistance m 2
        (prefixProduct m 2) 1 (by omega)).mpr
      exact hone
    omega
#print axioms pairwise_coprime_is_necessary

/-- Full capacity is necessary: with moduli two and three, restricting the message
range to two gives exact distance two although the full CRT product is six. -/
theorem full_dynamic_range_is_necessary :
    ∃ m : ℕ → ℕ,
      (∀ i, i < 2 → 1 < m i) ∧
      (∀ i j, i ≤ j → j < 2 → m i ≤ m j) ∧
      Nat.Coprime (m 0) (m 1) ∧
      2 < prefixProduct m 2 ∧
      residueMinimumDistance m 2 2 = 2 := by
  let m : ℕ → ℕ := fun i => if i = 0 then 2 else 3
  refine ⟨m, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [m]
    split <;> omega
  · intro i j hij hj
    simp only [m]
    split <;> split <;> omega
  · norm_num [m]
  · decide
  · have hminimumTwo : MinDistanceAtLeast m 2 2 2 := by
      intro x y hxy hy
      have hx : x = 0 := by omega
      have hy' : y = 1 := by omega
      subst x
      subst y
      decide
    have hlower : 2 ≤ residueMinimumDistance m 2 2 :=
      (minDistanceAtLeast_iff_le_residueMinimumDistance m 2 2 2 (by omega)).mp
        hminimumTwo
    have hwitness :
        hammingDist (residueWord m 2 0) (residueWord m 2 1) ∈
          {distance : ℕ | ∃ x y, x < y ∧ y < 2 ∧
            hammingDist (residueWord m 2 x) (residueWord m 2 y) = distance} := by
      exact ⟨0, 1, by omega, by omega, rfl⟩
    have hminimumLe :
        residueMinimumDistance m 2 2 ≤
          hammingDist (residueWord m 2 0) (residueWord m 2 1) := by
      unfold residueMinimumDistance
      exact Nat.sInf_le hwitness
    have hdistanceLe : hammingDist (residueWord m 2 0) (residueWord m 2 1) ≤ 2 := by
      simpa only [Fintype.card_fin] using
        (hammingDist_le_card_fintype :
          hammingDist (residueWord m 2 0) (residueWord m 2 1) ≤ Fintype.card (Fin 2))
    omega
#print axioms full_dynamic_range_is_necessary

end D5.S3.Arith.Coding.FullCRTDynamicRangeNoCorrectionMargin
