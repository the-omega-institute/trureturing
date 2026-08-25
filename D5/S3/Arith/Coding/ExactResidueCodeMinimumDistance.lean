/- GID: D5/S3/Arith/Coding/ExactResidueCodeMinimumDistance
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/ExactResidueCodeMinimumDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact residue-code distance is length minus the maximal blind-coordinate count. -/

import D5.S3.Arith.Coding.ResidueCodeDynamicRange
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Current-tree body-shape searches for an infimum of pairwise residue-word
     Hamming distances and for a powerset maximum constrained by a modulus product
     found no existing definitions. `ResidueCodeDynamicRange` is the family SSOT
     for `residueWord`, `MinDistanceAtLeast`, and `prefixProduct`.
   * The repository has no exact theorem equating minimum residue-code distance to
     the maximum cardinality of a product-bounded coordinate subset. The frozen
     `maximum_dynamic_range_iff_min_distance` instead supplies the adjacent sorted
     prefix thresholds used below.
   * Pinned Mathlib has no packaged minimum-distance object for a finite code.
     Exact reusable hits are `Nat.sInf_mem`, `Nat.sInf_le`, `Finset.exists_mem_eq_sup`,
     `Finset.map_orderEmbOfFin_univ`, and `hammingDist_le_card_fintype`; they supply
     the independently defined minimum, attained maximum, sorted enumeration, and
     ambient distance bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.ExactResidueCodeMinimumDistance

open D5.S3.Arith.Coding.ResidueCodeDynamicRange

/-- The infimum of Hamming distances between distinct messages in the bounded code. -/
noncomputable def residueMinimumDistance (m : ℕ → ℕ) (n K : ℕ) : ℕ :=
  sInf {distance | ∃ x y, x < y ∧ y < K ∧
    hammingDist (residueWord m n x) (residueWord m n y) = distance}

/-- The largest number of coordinates whose modulus product is below the dynamic range. -/
def maximumBlindCoordinateCount (m : ℕ → ℕ) (n K : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powerset.filter fun (coordinates : Finset (Fin n)) =>
      (∏ i ∈ coordinates, m (i : ℕ)) < K).sup Finset.card)

/-- On a nontrivial message range, the exact minimum is the largest universal lower
bound expressed by the canonical `MinDistanceAtLeast` predicate. -/
theorem minDistanceAtLeast_iff_le_residueMinimumDistance
    (m : ℕ → ℕ) (n K d : ℕ) (hK : 2 ≤ K) :
    MinDistanceAtLeast m n K d ↔ d ≤ residueMinimumDistance m n K := by
  have hnonempty :
      ({distance : ℕ | ∃ x y, x < y ∧ y < K ∧
        hammingDist (residueWord m n x) (residueWord m n y) = distance} : Set ℕ).Nonempty := by
    refine ⟨hammingDist (residueWord m n 0) (residueWord m n 1), 0, 1, ?_, ?_, rfl⟩
    · omega
    · omega
  constructor
  · intro hminimum
    have hattained := Nat.sInf_mem hnonempty
    change ∃ x y, x < y ∧ y < K ∧
      hammingDist (residueWord m n x) (residueWord m n y) =
        residueMinimumDistance m n K at hattained
    obtain ⟨x, y, hxy, hyK, hdistance⟩ := hattained
    simpa only [← hdistance] using hminimum x y hxy hyK
  · intro hd x y hxy hyK
    apply hd.trans
    unfold residueMinimumDistance
    apply Nat.sInf_le
    exact ⟨x, y, hxy, hyK, rfl⟩

/-- The subset maximum lies at the unique sorted-prefix threshold: its prefix product
is below `K`, while the next prefix product reaches `K`. -/
theorem maximumBlindCoordinateCount_prefix_bounds
    (m : ℕ → ℕ) (n K : ℕ)
    (hK : 2 ≤ K)
    (hKupper : K ≤ prefixProduct m n)
    (hmonotone : ∀ i j, i ≤ j → j < n → m i ≤ m j) :
    prefixProduct m (maximumBlindCoordinateCount m n K) < K ∧
      K ≤ prefixProduct m (maximumBlindCoordinateCount m n K + 1) := by
  let candidates : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset.filter fun (coordinates : Finset (Fin n)) =>
      (∏ i ∈ coordinates, m (i : ℕ)) < K
  have hempty : (∅ : Finset (Fin n)) ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
      Finset.prod_empty, true_and]
    omega
  have hcandidates : candidates.Nonempty := ⟨∅, hempty⟩
  obtain ⟨coordinates, hcoordinates, hmaximum⟩ :=
    Finset.exists_mem_eq_sup candidates hcandidates Finset.card
  have hcoordinateData := Finset.mem_filter.mp hcoordinates
  have hcard : coordinates.card = maximumBlindCoordinateCount m n K := by
    rw [maximumBlindCoordinateCount]
    exact hmaximum.symm
  let selection : Fin (maximumBlindCoordinateCount m n K) ↪o Fin n :=
    coordinates.orderEmbOfFin hcard
  have hprefix_le_selected :
      prefixProduct m (maximumBlindCoordinateCount m n K) ≤
        ∏ i : Fin (maximumBlindCoordinateCount m n K), m (selection i) := by
    simp only [prefixProduct]
    apply Finset.prod_le_prod
    · intro i _
      exact Nat.zero_le _
    · intro i _
      exact hmonotone i (selection i)
        (fin_index_le_strict_mono selection selection.strictMono i) (selection i).isLt
  have hselected_eq :
      (∏ i : Fin (maximumBlindCoordinateCount m n K), m (selection i)) =
        ∏ i ∈ coordinates, m (i : ℕ) := by
    rw [← Finset.map_orderEmbOfFin_univ coordinates hcard]
    rw [Finset.prod_map]
    rfl
  have hprefix_lt : prefixProduct m (maximumBlindCoordinateCount m n K) < K := by
    apply lt_of_le_of_lt hprefix_le_selected
    rw [hselected_eq]
    exact hcoordinateData.2
  have hcount_le_n : maximumBlindCoordinateCount m n K ≤ n := by
    rw [maximumBlindCoordinateCount]
    apply Finset.sup_le
    intro (subset : Finset (Fin n)) hsubset
    have hsubset_univ : subset ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hsubset).1
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsubset_univ
  have hcount_lt_n : maximumBlindCoordinateCount m n K < n := by
    by_contra hnot
    have heq : maximumBlindCoordinateCount m n K = n := Nat.le_antisymm hcount_le_n (by omega)
    rw [heq] at hprefix_lt
    omega
  refine ⟨hprefix_lt, ?_⟩
  by_contra hnext
  have hnext_lt : prefixProduct m (maximumBlindCoordinateCount m n K + 1) < K :=
    Nat.lt_of_not_ge hnext
  have hnext_le_n : maximumBlindCoordinateCount m n K + 1 ≤ n := by omega
  let prefixEmbedding : Fin (maximumBlindCoordinateCount m n K + 1) ↪ Fin n :=
    Fin.castLEEmb hnext_le_n
  let prefixCoordinates : Finset (Fin n) := Finset.univ.map prefixEmbedding
  have hprefixProduct :
      (∏ i ∈ prefixCoordinates, m (i : ℕ)) =
        prefixProduct m (maximumBlindCoordinateCount m n K + 1) := by
    dsimp only [prefixCoordinates]
    rw [Finset.prod_map]
    rfl
  have hprefixCoordinates : prefixCoordinates ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    rw [hprefixProduct]
    exact hnext_lt
  have hnext_card : prefixCoordinates.card = maximumBlindCoordinateCount m n K + 1 := by
    simp only [prefixCoordinates, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hnext_bounded : prefixCoordinates.card ≤ candidates.sup Finset.card :=
    Finset.le_sup hprefixCoordinates
  rw [hnext_card] at hnext_bounded
  have hcandidates_eq : candidates.sup Finset.card = maximumBlindCoordinateCount m n K := by
    simp only [candidates, maximumBlindCoordinateCount]
  rw [hcandidates_eq] at hnext_bounded
  omega

/-- For strictly increasing pairwise-coprime moduli at least two and a dynamic range
between two and the full modulus product, the exact bounded-code distance is the code
length minus the maximum number of simultaneously blind coordinates. -/
theorem exact_residue_code_minimum_distance
    (m : ℕ → ℕ) (n K : ℕ)
    (hmodulus : ∀ i, i < n → 2 ≤ m i)
    (hstrict : ∀ i j, i < j → j < n → m i < m j)
    (hcoprime : ∀ i j, i < n → j < n → i ≠ j → Nat.Coprime (m i) (m j))
    (hK : 2 ≤ K)
    (hKupper : K ≤ prefixProduct m n) :
    residueMinimumDistance m n K = n - maximumBlindCoordinateCount m n K := by
  let blind := maximumBlindCoordinateCount m n K
  have hmonotone : ∀ i j, i ≤ j → j < n → m i ≤ m j := by
    intro i j hij hjn
    rcases hij.eq_or_lt with (rfl | hij)
    · exact le_rfl
    · exact (hstrict i j hij hjn).le
  have hpositive : ∀ i, i < n → 0 < m i := by
    intro i hi
    exact lt_of_lt_of_le (by omega) (hmodulus i hi)
  have hblind_le : blind ≤ n := by
    simp only [blind, maximumBlindCoordinateCount]
    apply Finset.sup_le
    intro (coordinates : Finset (Fin n)) hcoordinates
    have hsubset : coordinates ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hcoordinates).1
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsubset
  have hprefix := maximumBlindCoordinateCount_prefix_bounds m n K hK hKupper hmonotone
  change prefixProduct m blind < K ∧ K ≤ prefixProduct m (blind + 1) at hprefix
  have hblind_lt : blind < n := by
    by_contra hnot
    have heq : blind = n := Nat.le_antisymm hblind_le (by omega)
    rw [heq] at hprefix
    omega
  have hlower : n - blind ≤ residueMinimumDistance m n K := by
    apply (minDistanceAtLeast_iff_le_residueMinimumDistance m n K (n - blind) hK).mp
    apply (maximum_dynamic_range_iff_min_distance m n (n - blind) K
      (by omega) (Nat.sub_le n blind) hmonotone hpositive hcoprime).mpr
    rw [show n - (n - blind) + 1 = blind + 1 by omega]
    exact hprefix.2
  have hupper : residueMinimumDistance m n K ≤ n - blind := by
    by_cases hblind : blind = 0
    · have hone_lt : (1 : ℕ) < K := by omega
      have hone_mem :
          hammingDist (residueWord m n 0) (residueWord m n 1) ∈
            {distance : ℕ | ∃ x y, x < y ∧ y < K ∧
              hammingDist (residueWord m n x) (residueWord m n y) = distance} :=
        ⟨0, 1, by omega, hone_lt, rfl⟩
      have hminimum_le : residueMinimumDistance m n K ≤
          hammingDist (residueWord m n 0) (residueWord m n 1) := by
        unfold residueMinimumDistance
        exact Nat.sInf_le hone_mem
      have hdistance_le :
          hammingDist (residueWord m n 0) (residueWord m n 1) ≤ n := by
        simpa only [Fintype.card_fin] using
          (hammingDist_le_card_fintype :
            hammingDist (residueWord m n 0) (residueWord m n 1) ≤ Fintype.card (Fin n))
      simpa only [hblind, Nat.sub_zero] using hminimum_le.trans hdistance_le
    · have hblind_pos : 1 ≤ blind := Nat.one_le_iff_ne_zero.mpr hblind
      have hsucc_le_n : n - blind + 1 ≤ n := by omega
      have hnotMinimum : ¬MinDistanceAtLeast m n K (n - blind + 1) := by
        intro hminimum
        have hbound := (maximum_dynamic_range_iff_min_distance m n (n - blind + 1) K
          (by omega) hsucc_le_n hmonotone hpositive hcoprime).mp hminimum
        have hbound' : K ≤ prefixProduct m blind := by
          rw [show n - (n - blind + 1) + 1 = blind by omega] at hbound
          exact hbound
        exact (Nat.not_le_of_gt hprefix.1) hbound'
      have hnotLe : ¬n - blind + 1 ≤ residueMinimumDistance m n K := by
        intro hle
        apply hnotMinimum
        exact (minDistanceAtLeast_iff_le_residueMinimumDistance
          m n K (n - blind + 1) hK).mpr hle
      omega
  exact Nat.le_antisymm hupper hlower

example :
    residueMinimumDistance (fun i => if i = 0 then 2 else 3) 2 2 =
      2 - maximumBlindCoordinateCount (fun i => if i = 0 then 2 else 3) 2 2 := by
  apply exact_residue_code_minimum_distance
  · intro i hi
    split <;> omega
  · intro i j hij hj
    split <;> split <;> omega
  · intro i j hi hj hij
    have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases hcases with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide
  · decide
  · decide

#print axioms exact_residue_code_minimum_distance

end D5.S3.Arith.Coding.ExactResidueCodeMinimumDistance
