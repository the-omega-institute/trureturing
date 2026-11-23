/- GID: D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrivatePairOmissionFamily
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Private pairs control intersections and survive restriction of the omitted family. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitWeightBlocks

/-! The finite family conditions separating omitted bases at a common pivot. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PrivatePairOmissionFamily

open Finset

set_option autoImplicit false

/-- Each member contains two distinct elements belonging to no other member. -/
def HasPrivatePairs {I : Type*} (family : Finset (Finset I)) : Prop :=
  ∀ F ∈ family, ∃ i ∈ F, ∃ j ∈ F, i ≠ j ∧
    ∀ G ∈ family, G ≠ F → i ∉ G ∧ j ∉ G

/-- Private elements for a family remain private for every subfamily. -/
theorem HasPrivatePairs.mono {I : Type*} {family selected : Finset (Finset I)}
    (h : HasPrivatePairs family) (hs : selected ⊆ family) : HasPrivatePairs selected := by
  intro F hF
  obtain ⟨i, hi, j, hj, hij, hprivate⟩ := h F (hs hF)
  exact ⟨i, hi, j, hj, hij, fun G hG hne => hprivate G (hs hG) hne⟩

/-- Pairs chosen in disjoint erased petals are private in the original family. -/
theorem HasPrivatePairs.of_disjoint_petals {I : Type*} [DecidableEq I]
    (family : Finset (Finset I)) (root : I)
    (hsize : ∀ F ∈ family, 1 < (F.erase root).card)
    (hdisjoint : (↑family : Set (Finset I)).Pairwise
      fun F G => Disjoint (F.erase root) (G.erase root)) :
    HasPrivatePairs family := by
  intro F hF
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (hsize F hF)
  refine ⟨i, mem_of_mem_erase hi, j, mem_of_mem_erase hj, hij, ?_⟩
  intro G hG hne
  have dis := hdisjoint hF hG hne.symm
  exact ⟨fun hiG => Finset.disjoint_left.mp dis hi (mem_erase.mpr ⟨ne_of_mem_erase hi, hiG⟩),
    fun hjG => Finset.disjoint_left.mp dis hj (mem_erase.mpr ⟨ne_of_mem_erase hj, hjG⟩)⟩

/-- Two omitted bases with private pairs share at most their size minus two
elements. The bound uses the size of the first member even for mixed sizes. -/
theorem HasPrivatePairs.inter_card_add_two_le {I : Type*} [DecidableEq I]
    {family : Finset (Finset I)} (h : HasPrivatePairs family) :
    (↑family : Set (Finset I)).Pairwise fun F G => (F ∩ G).card + 2 ≤ F.card := by
  intro F hF G hG hne
  obtain ⟨i, hi, j, hj, hij, hprivate⟩ := h F hF
  obtain ⟨hiG, hjG⟩ := hprivate G hG hne.symm
  have hiInter : i ∉ F ∩ G := fun ht => hiG (mem_inter.mp ht).2
  have hjInter : j ∉ F ∩ G := fun ht => hjG (mem_inter.mp ht).2
  have hiIns : i ∉ insert j (F ∩ G) := by simp [hij, hiInter]
  have hsub : insert i (insert j (F ∩ G)) ⊆ F :=
    insert_subset hi (insert_subset hj inter_subset_left)
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hiIns, card_insert_of_notMem hjInter] at hcard
  exact hcard

/-- After erasing a common pivot, the petals still contain private pairs.
For one omitted set it suffices that at least two elements remain. -/
theorem HasPrivatePairs.erase_exists {I : Type*} [DecidableEq I]
    {family : Finset (Finset I)} (h : HasPrivatePairs family) (root : I)
    (hroot : ∀ F ∈ family, root ∈ F) (hsize : ∀ F ∈ family, 1 < (F.erase root).card) :
    ∀ F ∈ family, ∃ i ∈ F.erase root, ∃ j ∈ F.erase root, i ≠ j ∧
      ∀ G ∈ family, G ≠ F → i ∉ G.erase root ∧ j ∉ G.erase root := by
  classical
  intro F hF
  by_cases hother : ∃ G ∈ family, G ≠ F
  · obtain ⟨G, hG, hne⟩ := hother
    obtain ⟨i, hi, j, hj, hij, hprivate⟩ := h F hF
    have hiRoot : i ≠ root := fun he => (hprivate G hG hne).1 (he.symm ▸ hroot G hG)
    have hjRoot : j ≠ root := fun he => (hprivate G hG hne).2 (he.symm ▸ hroot G hG)
    exact ⟨i, mem_erase.mpr ⟨hiRoot, hi⟩, j, mem_erase.mpr ⟨hjRoot, hj⟩, hij,
      fun U hU hUF => ⟨fun hiU => (hprivate U hU hUF).1 (mem_of_mem_erase hiU),
        fun hjU => (hprivate U hU hUF).2 (mem_of_mem_erase hjU)⟩⟩
  · obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (hsize F hF)
    exact ⟨i, hi, j, hj, hij, fun G hG hne => (hother ⟨G, hG, hne⟩).elim⟩

end D5.S3.Combinatorics.Matroids.PrivatePairOmissionFamily
