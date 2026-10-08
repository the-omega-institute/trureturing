/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicValley
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicValley
   mirror-E: none(waiver:valley-maximum-insertion-witness)
   anchors: []
   utility: none
   digest: A maximum inserted after one preserves a decreasing suffix only immediately after one. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicValley

theorem maximum_insertion_valley_iff (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (one site : ℕ)
    (hone : one < site) (hsite : site ≤ p.length) :
    (∀ earlier later, one < earlier → earlier < later →
      later < (p.insertIdx site (n + 1)).length →
        (p.insertIdx site (n + 1)).getD later 0 <
          (p.insertIdx site (n + 1)).getD earlier 0) ↔
      (∀ earlier later, one < earlier → earlier < later → later < p.length →
        p.getD later 0 < p.getD earlier 0) ∧ site = one + 1 := by
  let child := p.insertIdx site (n + 1)
  let lift := fun index : ℕ => if index < site then index else index + 1
  have hlen : child.length = p.length + 1 := List.length_insertIdx_of_le_length hsite _
  have hbound (index : ℕ) (hi : index < p.length) : p.getD index 0 < n + 1 := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hrange := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, heq⟩ := hrange
    omega
  have hbefore (index : ℕ) (hi : index < site) : child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hafter (index : ℕ) (hi : site < index) (hb : index < child.length) :
      child.getD index 0 = p.getD (index - 1) 0 := by
    rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hliftbound (index : ℕ) (hi : index < p.length) : lift index < child.length := by
    dsimp [lift]
    split_ifs <;> omega
  have hliftentry (index : ℕ) (hi : index < p.length) :
      child.getD (lift index) 0 = p.getD index 0 := by
    dsimp [lift]
    split_ifs with hlt
    · exact hbefore index hlt
    · simpa only [Nat.add_sub_cancel] using hafter (index + 1) (by omega) (by omega)
  change (∀ earlier later, one < earlier → earlier < later → later < child.length →
    child.getD later 0 < child.getD earlier 0) ↔ _
  constructor
  · intro hchild
    constructor
    · intro earlier later he hl hb
      have hlifte : one < lift earlier := by dsimp [lift]; split_ifs <;> omega
      have hliftorder : lift earlier < lift later := by dsimp [lift]; split_ifs <;> omega
      have hh := hchild (lift earlier) (lift later) hlifte hliftorder (hliftbound later hb)
      rwa [hliftentry later hb, hliftentry earlier (by omega)] at hh
    · by_contra hnot
      have hlt : one + 1 < site := by omega
      have hh := hchild (one + 1) site (by omega) hlt (by omega)
      rw [hat, hbefore (one + 1) hlt] at hh
      have hb := hbound (one + 1) (by omega)
      omega
  · rintro ⟨hparent, hsiteone⟩ earlier later he hl hb
    have hearliersite : site ≤ earlier := by omega
    by_cases heq : earlier = site
    · subst earlier
      rw [hat, hafter later (by omega) hb]
      exact hbound (later - 1) (by omega)
    · rw [hafter later (by omega) hb, hafter earlier (by omega) (by omega)]
      exact hparent (earlier - 1) (later - 1) (by omega) (by omega) (by omega)

end D5.S3.Combinatorics.Fishburn.FishburnBasicValley
