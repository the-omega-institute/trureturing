/- GID: D5/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity
   mirror-E: none(waiver:general-rank-rigidity)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Sharp chain bounds force rank rigidity in odd Boolean lattices. -/

import D5.S3.Combinatorics.ErdosUlam.SublatticeDefs
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Nodup

namespace D5.S3.Combinatorics.ErdosUlam.SublatticeRankRigidity

open D5.S3.Combinatorics.ErdosUlam.SublatticeDefs

open Finset

private def listPrefix {n : ℕ} (l : List (Fin n)) (r : ℕ) : Finset (Fin n) :=
  (l.take r).toFinset

private theorem listPrefix_card {n : ℕ} {l : List (Fin n)} (hl : l.Nodup)
    {r : ℕ} (hr : r ≤ l.length) : (listPrefix l r).card = r := by
  rw [listPrefix, List.toFinset_card_of_nodup (hl.take), List.length_take,
    Nat.min_eq_left hr]

private theorem listPrefix_subset {n : ℕ} (l : List (Fin n)) {r s : ℕ}
    (h : r ≤ s) : listPrefix l r ⊆ listPrefix l s := by
  intro x hx
  simp only [listPrefix, List.mem_toFinset] at hx ⊢
  exact List.take_subset_take_left l h hx

private theorem chain_colour_bound {n : ℕ} (χ : Finset (Fin n) → Bool)
    (hs : ∀ L, IsSublattice L → Monochromatic χ L → L.card ≤ (n + 1) / 2)
    (l : List (Fin n)) (hl : l.Nodup) (hlen : l.length = n) (c : Bool) :
    ((range (n + 1)).filter (fun r => χ (listPrefix l r) = c)).card ≤ (n + 1) / 2 := by
  classical
  let R := (range (n + 1)).filter (fun r => χ (listPrefix l r) = c)
  by_cases hR : R.Nonempty
  · let L := R.image (listPrefix l)
    have hsub : IsSublattice L := by
      refine ⟨hR.image _, ?_⟩
      intro A hA B hB
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hA
      obtain ⟨s, hs', rfl⟩ := mem_image.mp hB
      rcases le_total r s with hrs | hsr
      · have h := listPrefix_subset l hrs
        exact ⟨by simpa only [union_eq_right.mpr h] using mem_image.mpr ⟨s, hs', rfl⟩,
          by simpa only [inter_eq_left.mpr h] using mem_image.mpr ⟨r, hr, rfl⟩⟩
      · have h := listPrefix_subset l hsr
        exact ⟨by simpa only [union_eq_left.mpr h] using mem_image.mpr ⟨r, hr, rfl⟩,
          by simpa only [inter_eq_right.mpr h] using mem_image.mpr ⟨s, hs', rfl⟩⟩
    have hm : Monochromatic χ L := by
      refine ⟨c, ?_⟩
      intro A hA
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hA
      exact (mem_filter.mp hr).2
    have hc : L.card = R.card := by
      apply card_image_iff.mpr
      intro r hr s hs' he
      have hr' : r ≤ l.length := by have := (mem_range.mp (mem_filter.mp hr).1); omega
      have hs'' : s ≤ l.length := by have := (mem_range.mp (mem_filter.mp hs').1); omega
      simpa only [listPrefix_card hl hr', listPrefix_card hl hs''] using congrArg card he
    rw [← hc]
    exact hs L hsub hm
  · have : R = ∅ := not_nonempty_iff_eq_empty.mp hR
    change R.card ≤ _
    simp [this]

/-- Every maximal chain has the same number of sets of each colour under the sharp bound. -/
private theorem balanced_chain {n : ℕ} (hodd : Odd n) (χ : Finset (Fin n) → Bool)
    (hs : ∀ L, IsSublattice L → Monochromatic χ L → L.card ≤ (n + 1) / 2)
    (l : List (Fin n)) (hl : l.Nodup) (hlen : l.length = n) (c : Bool) :
    ((range (n + 1)).filter (fun r => χ (listPrefix l r) = c)).card = (n + 1) / 2 := by
  classical
  have h₁ := chain_colour_bound χ hs l hl hlen c
  have h₂ := chain_colour_bound χ hs l hl hlen (!c)
  have hsum := card_filter_add_card_filter_not (s := range (n + 1))
    (fun r => χ (listPrefix l r) = c)
  have he : ((range (n + 1)).filter (fun r => ¬χ (listPrefix l r) = c)) =
      ((range (n + 1)).filter (fun r => χ (listPrefix l r) = !c)) := by
    apply filter_congr
    intro r _
    cases c <;> cases χ (listPrefix l r) <;> simp
  rw [he, card_range] at hsum
  rcases hodd with ⟨k, hk⟩
  omega

private theorem exchange_colour {n : ℕ} (hodd : Odd n)
    (χ : Finset (Fin n) → Bool)
    (hs : ∀ L, IsSublattice L → Monochromatic χ L → L.card ≤ (n + 1) / 2)
    (l l' : List (Fin n)) (hl : l.Nodup) (hl' : l'.Nodup)
    (hlen : l.length = n) (hlen' : l'.length = n) (r : ℕ) (hr : r ≤ n)
    (he : ∀ s, s ≠ r → listPrefix l s = listPrefix l' s) :
    χ (listPrefix l r) = χ (listPrefix l' r) := by
  classical
  let c := χ (listPrefix l r)
  have h₁ := balanced_chain hodd χ hs l hl hlen c
  have h₂ := balanced_chain hodd χ hs l' hl' hlen' c
  have her : ((range (n + 1)).erase r).filter (fun s => χ (listPrefix l s) = c) =
      ((range (n + 1)).erase r).filter (fun s => χ (listPrefix l' s) = c) := by
    ext s
    by_cases hsr : s = r
    · simp [hsr]
    · simp only [mem_filter, mem_erase]
      rw [he s hsr]
  have hins : insert r ((range (n + 1)).erase r) = range (n + 1) :=
    insert_erase (mem_range.mpr (by omega))
  rw [← hins, filter_insert, if_pos (show χ (listPrefix l r) = c from rfl),
    card_insert_of_notMem (by simp)] at h₁
  by_contra hne
  have hnc : χ (listPrefix l' r) ≠ c := Ne.symm hne
  rw [← hins, filter_insert, if_neg hnc] at h₂
  rw [her] at h₁
  omega

private theorem adjacent_colour {n : ℕ} (hodd : Odd n)
    (χ : Finset (Fin n) → Bool)
    (hs : ∀ L, IsSublattice L → Monochromatic χ L → L.card ≤ (n + 1) / 2)
    (C : Finset (Fin n)) (x y : Fin n) (hx : x ∉ C) (hy : y ∉ C) (hxy : x ≠ y) :
    χ (insert x C) = χ (insert y C) := by
  classical
  let D := (insert x (insert y C))ᶜ
  let l := C.toList ++ [x,y] ++ D.toList
  let l' := C.toList ++ [y,x] ++ D.toList
  have hnod : l.Nodup := by
    simp only [l, List.nodup_append, List.nodup_cons, List.nodup_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
      and_true, nodup_toList, List.mem_append, mem_toList]
    simp [D, hxy, ne_comm]
    grind
  have hnod' : l'.Nodup := by
    simp only [l', List.nodup_append, List.nodup_cons, List.nodup_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
      and_true, nodup_toList, List.mem_append, mem_toList]
    simp [D, hxy, ne_comm]
    grind
  have hlen : l.length = n := by
    have hc : (insert x (insert y C)).card = C.card + 2 := by simp [hx, hy, hxy]
    have hD : D.card + (insert x (insert y C)).card = n := by
      simpa [D] using card_compl_add_card (insert x (insert y C))
    simp only [l, List.length_append, List.length_cons, List.length_nil, length_toList]
    omega
  have hlen' : l'.length = n := by simpa only [l, l', List.length_append,
      List.length_cons, List.length_nil, length_toList] using hlen
  have hr : C.card + 1 ≤ n := by
    have hc := card_le_univ (insert x (insert y C))
    simp [hx, hy, hxy] at hc
    omega
  have hpre : listPrefix l (C.card + 1) = insert x C := by
    have ht : C.toList.length ≤ C.card + 1 := by simp
    simp [listPrefix, l, List.take_append, List.take_of_length_le ht]
  have hpre' : listPrefix l' (C.card + 1) = insert y C := by
    have ht : C.toList.length ≤ C.card + 1 := by simp
    simp [listPrefix, l', List.take_append, List.take_of_length_le ht]
  have he : ∀ s, s ≠ C.card + 1 → listPrefix l s = listPrefix l' s := by
    intro s hsr
    by_cases hsC : s ≤ C.card
    · simp [listPrefix, l, l', List.take_append, Nat.sub_eq_zero_of_le hsC]
    · have hge : C.card + 2 ≤ s := by omega
      have hs1 : s - C.card ≥ 2 := by omega
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hs1
      have hst : s - C.card = t + 2 := by omega
      simp [listPrefix, l, l', List.take_append, hst, insert_comm]
  simpa only [hpre, hpre'] using exchange_colour hodd χ hs l l' hnod hnod'
    hlen hlen' (C.card + 1) hr he

/-- Equal-rank sets have equal colours: one-element exchanges connect each rank. -/
theorem rank_rigidity {n : ℕ} (hodd : Odd n) (χ : Finset (Fin n) → Bool)
    (hs : ∀ L, IsSublattice L → Monochromatic χ L → L.card ≤ (n + 1) / 2) :
    ∀ A B : Finset (Fin n), A.card = B.card → χ A = χ B := by
  classical
  intro A B hcard
  generalize hk : (A \ B).card = k
  induction k using Nat.strong_induction_on generalizing A with
  | h k ih =>
    by_cases hk0 : k = 0
    · have hsub : A ⊆ B := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (hk.trans hk0))
      rw [eq_of_subset_of_card_le hsub hcard.ge]
    · obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (A \ B).card by omega)
      have hxA := (mem_sdiff.mp hx).1
      have hxB := (mem_sdiff.mp hx).2
      have hdiff : (B \ A).card = (A \ B).card := card_sdiff_comm hcard.symm
      obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (B \ A).card by omega)
      have hyB := (mem_sdiff.mp hy).1
      have hyA := (mem_sdiff.mp hy).2
      let C := A.erase x
      let A' := insert y C
      have hxC : x ∉ C := by simp [C]
      have hyC : y ∉ C := by simp [C, hyA]
      have hxy : x ≠ y := by intro h; exact hyA (h ▸ hxA)
      have heq := adjacent_colour hodd χ hs C x y hxC hyC hxy
      have hA : insert x C = A := insert_erase hxA
      have hcard' : A'.card = B.card := by
        simp only [A', card_insert_of_notMem hyC, C, card_erase_of_mem hxA]
        have hp := card_pos.mpr ⟨x, hxA⟩
        omega
      have hdiff' : A' \ B = (A \ B).erase x := by
        ext z
        simp only [A', C, mem_sdiff, mem_insert, mem_erase]
        constructor
        · rintro ⟨hz | hz, hzb⟩
          · exact False.elim (hzb (hz ▸ hyB))
          · exact ⟨hz.1, hz.2, hzb⟩
        · rintro ⟨hzx, hzA, hzb⟩
          exact ⟨Or.inr ⟨hzx, hzA⟩, hzb⟩
      have hlt : (A' \ B).card < k := by
        rw [hdiff']
        exact hk ▸ card_erase_lt_of_mem hx
      have hrec := ih (A' \ B).card hlt A' hcard' rfl
      rw [hA] at heq
      exact heq.trans hrec

/-- The rank colouring forced by rigidity is balanced on the standard prefix chain. -/
theorem balanced_prefixes {n : ℕ} (hodd : Odd n) (χ : Finset (Fin n) → Bool)
    (hs : ∀ L, IsSublattice L → Monochromatic χ L → L.card ≤ (n + 1) / 2)
    (c : Bool) :
    ((range (n + 1)).filter (fun r => χ (initialSegment n r) = c)).card = (n + 1) / 2 := by
  classical
  have h := balanced_chain hodd χ hs (List.finRange n) (List.nodup_finRange n)
    (by simp) c
  have he : ∀ r, listPrefix (List.finRange n) r = initialSegment n r := by
    intro r
    ext i
    simp only [listPrefix, initialSegment, List.mem_toFinset, mem_filter, mem_univ, true_and]
    simp only [List.mem_take_iff_getElem, List.getElem_finRange, List.length_finRange,
      lt_min_iff]
    constructor
    · rintro ⟨j, hj, he⟩
      have hji := congrArg Fin.val he
      change j = i.val at hji
      omega
    · intro hi
      exact ⟨i.val, ⟨hi, i.isLt⟩, Fin.ext rfl⟩
  simpa only [he] using h

end D5.S3.Combinatorics.ErdosUlam.SublatticeRankRigidity
