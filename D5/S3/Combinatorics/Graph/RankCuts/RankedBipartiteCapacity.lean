/- GID: D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank capacities force charged diagonal multiplicity. -/

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Rank prefixes and suffixes bound charged diagonal multiplicities. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
private theorem restricted_column_bound (e : V → V → ℕ) (K P E : Finset V)
    (off : ∀ a b, a ∉ K → b ∈ P → e a b ≠ 0 → a = b ∧ a ∈ E) :
    (∑ b ∈ P, ∑ a, e a b) ≤ (∑ a ∈ K, ∑ b ∈ P, e a b) + ∑ a ∈ E, e a a := by
  classical
  have as_sum_over_all (S : Finset V) (f : V → ℕ) :
      (∑ a ∈ S, f a) = ∑ a, if a ∈ S then f a else 0 := by
    rw [← sum_filter]
    congr 1
    ext a
    simp
  rw [sum_comm (s := P) (t := univ), as_sum_over_all K, as_sum_over_all E, ← sum_add_distrib]
  refine sum_le_sum fun a _ => ?_
  by_cases hK : a ∈ K
  · rw [ite_eq_left hK]
    exact Nat.le_add_right _ _
  · simp only [hK, ite_false, zero_add]
    by_cases hE : a ∈ E
    · rw [ite_eq_left hE]
      refine (sum_le_sum (f := e a) (g := fun b => if b = a then e a a else 0)
        fun b hb => ?_).trans ?_
      · by_cases h : b = a
        · subst b
          simp
        · have hz : e a b = 0 := by
            by_contra hn
            exact h (off a b hK hb hn).1.symm
          simp [h, hz]
      · rw [sum_ite_eq']
        by_cases ha : a ∈ P <;> simp [ha]
    · rw [ite_eq_right hE, Nat.le_zero]
      refine sum_eq_zero fun b hb => ?_
      by_contra hn
      exact hE (off a b hK hb hn).2

private def strictLower (rank : V → ℕ) (r : ℕ) := univ.filter fun a => rank a < r
private def strictUpper (rank : V → ℕ) (r : ℕ) := univ.filter fun a => r < rank a
private def sameRank (rank : V → ℕ) (r : ℕ) := univ.filter fun a => rank a = r
private def lowerClosure (rank : V → ℕ) (r : ℕ) := univ.filter fun a => rank a ≤ r
private def upperClosure (rank : V → ℕ) (r : ℕ) (top : V) :=
  univ.filter fun a => r ≤ rank a ∧ a ≠ top

omit [DecidableEq V] [Fintype V] in
private theorem degree_lower (d : V → ℕ) (S : Finset V)
    (h : ∀ a ∈ S, 1 ≤ d a) : S.card ≤ ∑ a ∈ S, d a := by
  simpa using sum_le_sum h

omit [DecidableEq V] [Fintype V] in
private theorem degree_upper (d : V → ℕ) (S : Finset V) (k : ℕ)
    (h : ∀ a ∈ S, d a ≤ k) : (∑ a ∈ S, d a) ≤ S.card * k := by
  simpa [Nat.nsmul_eq_mul] using sum_le_sum h

omit [DecidableEq V] in
private theorem prefix_capacity_with_actual_inflow (rank : V → ℕ) (top : V) (r k : ℕ)
    (e : V → V → ℕ)
    (topAbove : r < rank top)
    (ordinary : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank a < rank b)
    (colMin : ∀ b ∈ lowerClosure rank r, 1 ≤ ∑ a, e a b)
    (rowMax : ∀ a ∈ strictLower rank r, (∑ b, e a b) ≤ k) :
    (lowerClosure rank r).card ≤
      (strictLower rank r).card * k + (∑ b ∈ lowerClosure rank r, e top b) +
        ∑ a ∈ sameRank rank r, e a a := by
  classical
  let L := strictLower rank r
  let P := lowerClosure rank r
  let E := sameRank rank r
  have topOut : top ∉ L := by simp [L, strictLower]; omega
  have restricted := restricted_column_bound e (insert top L) P E (by
    intro a b hK hb he
    have hTop : a ≠ top := fun ha => hK (ha ▸ mem_insert_self _ _)
    have hL : r ≤ rank a := by
      by_contra h
      exact hK (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, by omega⟩))
    have hP : rank b ≤ r := (mem_filter.mp hb).2
    rcases ordinary a b hTop he with h | h
    · refine ⟨h, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      rw [h] at hL ⊢
      omega
    · omega)
  rw [sum_insert topOut] at restricted
  have lower := degree_lower (fun b => ∑ a, e a b) P colMin
  have upper := degree_upper (fun a => ∑ b ∈ P, e a b) L k
    (fun a ha => (sum_le_sum_of_subset_of_nonneg (s := P) (t := univ) (f := e a)
      (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans (rowMax a ha))
  change P.card ≤ L.card * k + (∑ b ∈ P, e top b) + ∑ a ∈ E, e a a
  omega

/-- Capacities on the two sides of a rank force diagonal multiplicity even when
    ordinary edges skip arbitrarily many ranks. -/
private theorem two_sided_rank_capacity (rank : V → ℕ) (top : V) (r k ka kb : ℕ)
    (e : V → V → ℕ)
    (topAbove : r < rank top)
    (ordinary : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank a < rank b)
    (rowMin : ∀ a ≠ top, 1 ≤ ∑ b, e a b)
    (colMin : ∀ b ≠ top, 1 ≤ ∑ a, e a b)
    (rowMax : ∀ a ≠ top, (∑ b, e a b) ≤ k)
    (colMax : ∀ b ≠ top, (∑ a, e a b) ≤ k)
    (topRow : (∑ b, e top b) ≤ ka)
    (topCol : (∑ a, e a top) ≤ kb) :
    max ((lowerClosure rank r).card - ((strictLower rank r).card * k + ka))
        ((upperClosure rank r top).card - (((strictUpper rank r).erase top).card * k + kb))
      ≤ ∑ a ∈ sameRank rank r, e a a := by
  apply max_le
  · let L := strictLower rank r
    let P := lowerClosure rank r
    let E := sameRank rank r
    have rankBound := prefix_capacity_with_actual_inflow rank top r k e topAbove ordinary
      (fun b hb => colMin b (by
        intro h
        subst b
        exact (not_le_of_gt topAbove) (mem_filter.mp hb).2))
      (fun a ha => rowMax a (by
        intro h
        subst a
        have hlt := (mem_filter.mp ha).2
        omega))
    have inflowBound : (∑ b ∈ P, e top b) ≤ ka :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans topRow
    change P.card ≤ L.card * k + (∑ b ∈ P, e top b) + ∑ a ∈ E, e a a at rankBound
    change P.card - (L.card * k + ka) ≤ ∑ a ∈ E, e a a
    omega
  · let H := strictUpper rank r
    let P := upperClosure rank r top
    let E := sameRank rank r
    have topIn : top ∈ H := mem_filter.mpr ⟨mem_univ _, topAbove⟩
    have sumBound := restricted_column_bound (fun b a => e a b) H P E (by
      intro b a hH ha he
      obtain ⟨ge, hTop⟩ := (mem_filter.mp ha).2
      have le : rank b ≤ r := by
        by_contra h
        exact hH (mem_filter.mpr ⟨mem_univ _, by omega⟩)
      rcases ordinary a b hTop he with h | h
      · refine ⟨h.symm, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
        rw [h] at ge
        omega
      · omega)
    rw [← sum_erase_add _ _ topIn] at sumBound
    have lower := degree_lower (fun a => ∑ b, e a b) P
      (fun a h => rowMin a (mem_filter.mp h).2.2)
    have upper := degree_upper (fun b => ∑ a ∈ P, e a b) (H.erase top) k
      (fun b h => (sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun _ _ _ => Nat.zero_le _)).trans (colMax b (mem_erase.mp h).1))
    have topCol' : (∑ a ∈ P, e a top) ≤ kb :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans topCol
    change P.card - ((H.erase top).card * k + kb) ≤ ∑ a ∈ E, e a a
    omega

/-- Disjoint odd diagonal layers can be charged simultaneously. -/
theorem paid_edges_ge_rank_capacity (rank : V → ℕ) (top : V) (k ka kb : ℕ)
    (e : V → V → ℕ) (R : Finset ℕ)
    (eligible : ∀ r ∈ R, r < rank top ∧ r % 2 = 1)
    (ordinary : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank a < rank b)
    (rowMin : ∀ a ≠ top, 1 ≤ ∑ b, e a b)
    (colMin : ∀ b ≠ top, 1 ≤ ∑ a, e a b)
    (rowMax : ∀ a ≠ top, (∑ b, e a b) ≤ k)
    (colMax : ∀ b ≠ top, (∑ a, e a b) ≤ k)
    (topRow : (∑ b, e top b) ≤ ka)
    (topCol : (∑ a, e a top) ≤ kb) :
    (∑ r ∈ R, max ((lowerClosure rank r).card - ((strictLower rank r).card * k + ka))
        ((upperClosure rank r top).card - (((strictUpper rank r).erase top).card * k + kb)))
      ≤ ∑ a, ∑ b, if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then e a b else 0 := by
  calc
    _ ≤ ∑ r ∈ R, ∑ a ∈ sameRank rank r, e a a := sum_le_sum fun r hr =>
      two_sided_rank_capacity rank top r k ka kb e (eligible r hr).1 ordinary
        rowMin colMin rowMax colMax topRow topCol
    _ = ∑ a, if rank a ∈ R then e a a else 0 := by
      unfold sameRank
      rw [sum_fiberwise_eq_sum_filter, sum_filter]
    _ ≤ _ := by
      refine sum_le_sum fun a _ => ?_
      by_cases ha : rank a ∈ R
      · rw [ite_eq_left ha]
        have noTop : a ≠ top := fun h => (Nat.lt_irrefl (rank top))
          (by simpa [h] using (eligible (rank a) ha).1)
        let cost (b : V) := if a ≠ top ∧ rank a % 2 = 1 ∧ rank b % 2 = 1 then e a b else 0
        have h := single_le_sum (f := cost) (fun _ _ => Nat.zero_le _) (mem_univ a)
        simpa [cost, noTop, (eligible (rank a) ha).2] using h
      · simp [ha]

end D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteCapacity
