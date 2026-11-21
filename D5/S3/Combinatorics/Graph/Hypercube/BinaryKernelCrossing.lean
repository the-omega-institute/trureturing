/- GID: D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Even cube rows force enough distance-three support to cover the crossing pairs. -/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Crossing pairs bound binary adjacency-kernel support in the coordinate-subset cube. -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCrossing

open Finset
open scoped BigOperators symmDiff

variable {n : ℕ}

/-- In the coordinate-subset model of the cube, these are the directions whose
single flip of `x` belongs to the support `R`. Flipping is symmetric difference. -/
def neighborDirections (R : Finset (Finset (Fin n))) (x : Finset (Fin n)) :
    Finset (Fin n) :=
  univ.filter fun i => x ∆ {i} ∈ R

private theorem two_le_of_even_pos {m : ℕ} (he : Even m) (hm : 0 < m) : 2 ≤ m := by
  obtain ⟨a, ha⟩ := he
  omega

private theorem crossingPairs_card_le_two (S t : Finset (Fin n)) (ht : t.card = 3) :
    ((t ∩ S) ×ˢ (t \ S)).card ≤ 2 := by
  rw [card_product]
  have h := card_inter_add_card_sdiff t S
  have hc : (t ∩ S).card = 0 ∨ (t ∩ S).card = 1 ∨ (t ∩ S).card = 2 ∨
      (t ∩ S).card = 3 := by omega
  rcases hc with h₀ | h₁ | h₂ | h₃
  · simp [h₀]
  · simp only [h₁, one_mul]
    omega
  · simp only [h₂]
    omega
  · have hz : (t \ S).card = 0 := by omega
    simp [hz]

/-- At any pivot, even support degrees at the two-flip vertices force
`k * (n - k) ≤ 2 * |R₃|`, where `k` counts the selected one-flip
neighbors and `R₃` is the support at Hamming distance three. The same
crossing count plus the one-flip contribution bounds the total support. -/
theorem crossing_pair_bounds (R : Finset (Finset (Fin n))) (x : Finset (Fin n))
    (hrows : ∀ y : Finset (Fin n), (x ∆ y).card = 2 →
      Even (neighborDirections R y).card) :
    let k := (neighborDirections R x).card
    k * (n - k) ≤ 2 * (R.filter fun y => (x ∆ y).card = 3).card ∧
      2 * k + k * (n - k) ≤ 2 * R.card := by
  dsimp only
  let S := neighborDirections R x
  let T := R.filter fun y => (x ∆ y).card = 3
  let cover (y : Finset (Fin n)) := ((x ∆ y) ∩ S) ×ˢ ((x ∆ y) \ S)
  have hall : S ×ˢ (univ \ S) ⊆ T.biUnion cover := by
    rintro ⟨i, j⟩ hp
    obtain ⟨hi, hj⟩ := mem_product.mp hp
    have hjS := (mem_sdiff.mp hj).2
    have hiR : x ∆ {i} ∈ R := (mem_filter.mp hi).2
    have hjR : x ∆ {j} ∉ R := fun h => hjS (mem_filter.mpr ⟨mem_univ _, h⟩)
    have hij : i ≠ j := fun h => hjS (h ▸ hi)
    have hpair : ({i, j} : Finset (Fin n)) = {i} ∆ {j} := by
      rw [Finset.symmDiff_eq_union (disjoint_singleton.mpr hij), singleton_union]
    let y := x ∆ ({i, j} : Finset (Fin n))
    have hy : x ∆ y = {i, j} := symmDiff_symmDiff_cancel_left _ _
    have hrowsy := hrows y (by rw [hy, card_pair hij])
    have hyj : y ∆ {j} = x ∆ {i} := by
      simp [y, hpair, symmDiff_assoc]
    have hyi : y ∆ {i} = x ∆ {j} := by
      change (x ∆ ({i, j} : Finset (Fin n))) ∆ {i} = x ∆ {j}
      rw [hpair, symmDiff_comm ({i} : Finset (Fin n)) {j}]
      simp [symmDiff_assoc]
    have hjy : j ∈ neighborDirections R y := by
      simpa [neighborDirections, hyj] using hiR
    have hiy : i ∉ neighborDirections R y := by
      simpa [neighborDirections, hyi] using hjR
    have htwo := two_le_of_even_pos hrowsy (card_pos.mpr ⟨j, hjy⟩)
    obtain ⟨a, ha⟩ : ((neighborDirections R y).erase j).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hjy]
      omega
    obtain ⟨haj, hay⟩ := mem_erase.mp ha
    have hai : a ≠ i := fun h => hiy (h ▸ hay)
    have haPair : a ∉ ({i, j} : Finset (Fin n)) := by simp [hai, haj]
    have hoffset : x ∆ (y ∆ {a}) = insert a {i, j} := by
      rw [← symmDiff_assoc, hy, symmDiff_comm, Finset.symmDiff_eq_union
        (disjoint_singleton_left.mpr haPair), singleton_union]
    apply mem_biUnion.mpr
    refine ⟨y ∆ {a}, mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa [neighborDirections] using hay
    · rw [hoffset, card_insert_of_notMem haPair, card_pair hij]
    · simp [cover, hoffset, hi, hjS]
  have hcross : S.card * (n - S.card) ≤ 2 * T.card := calc
    _ = (S ×ˢ (univ \ S)).card := by
      rw [card_product, card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]
    _ ≤ (T.biUnion cover).card := card_le_card hall
    _ ≤ ∑ y ∈ T, (cover y).card := card_biUnion_le
    _ ≤ ∑ _y ∈ T, 2 := sum_le_sum fun y hy =>
      crossingPairs_card_le_two S (x ∆ y) (mem_filter.mp hy).2
    _ = _ := by simp [Nat.mul_comm]
  let L := R.filter fun y => (x ∆ y).card = 1
  have hL : S.card ≤ L.card := by
    apply card_le_card_of_injOn (fun i => x ∆ {i})
    · intro i hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).2, by simp⟩
    · intro i _ j _ h
      have he := congrArg (fun t : Finset (Fin n) => x ∆ t) h
      simpa using he
  have hLT : L.card + T.card ≤ R.card := by
    have hd : Disjoint L T := by
      apply disjoint_left.mpr
      intro y hy hz
      have h₁ := (mem_filter.mp hy).2
      have h₃ := (mem_filter.mp hz).2
      omega
    rw [← card_union_of_disjoint hd]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  change S.card * (n - S.card) ≤ 2 * T.card ∧
    2 * S.card + S.card * (n - S.card) ≤ 2 * R.card
  exact ⟨hcross, by omega⟩

/-- A nonempty binary adjacency-kernel support has weight at least the cube dimension. -/
theorem card_ge_dimension (R : Finset (Finset (Fin n))) (hR : R.Nonempty)
    (hrows : ∀ y, Even (neighborDirections R y).card) : n ≤ R.card := by
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨r, hr⟩ := hR
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let x := r ∆ ({i} : Finset (Fin n))
  let k := (neighborDirections R x).card
  have hi : i ∈ neighborDirections R x := by simpa [neighborDirections, x] using hr
  have hk₂ : 2 ≤ k := two_le_of_even_pos (hrows x) (card_pos.mpr ⟨i, hi⟩)
  have hkₙ : k ≤ n := by simpa [k] using card_le_univ (neighborDirections R x)
  have hbound : 2 * k + k * (n - k) ≤ 2 * R.card :=
    (crossing_pair_bounds R x fun y _ => hrows y).2
  have hmul := Nat.mul_le_mul_right (n - k) hk₂
  have hsum : 2 * (n - k) + 2 * k = 2 * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hkₙ]
  omega

end D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCrossing
