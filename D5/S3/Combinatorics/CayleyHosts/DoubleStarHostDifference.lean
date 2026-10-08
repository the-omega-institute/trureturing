/- GID: D5/S3/Combinatorics/CayleyHosts/DoubleStarHostDifference
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleyHosts/DoubleStarHostDifference
   mirror-E: none(waiver:additive-counting)
   anchors: [mathlib/module/Mathlib.Combinatorics.Additive.VerySmallDoubling]
   utility: none
   digest: A finite set with difference doubling below three halves has subgroup differences. -/
import Mathlib.Combinatorics.Additive.VerySmallDoubling

open scoped Pointwise

namespace D5.S3.Combinatorics.CayleyHosts.DoubleStarHostDifference

/-- Two intersection counts force closure of a sufficiently small difference set. -/
theorem difference_subgroup {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (L : Finset Γ) (hne : L.Nonempty) (hsmall : 2 * (L - L).card < 3 * L.card) :
    ∃ H : AddSubgroup Γ, (H : Set Γ) = ↑(L - L) := by
  classical
  have hdense (d : Γ) (hd : d ∈ L - L) :
      L.card < 2 * (L.filter fun z => z - d ∈ L).card := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hd
    let P := L.image (fun z => z - a)
    let Q := L.image (fun z => z - b)
    have hP : P.card = L.card :=
      Finset.card_image_of_injective L (fun _ _ h => sub_left_injective h)
    have hQ : Q.card = L.card :=
      Finset.card_image_of_injective L (fun _ _ h => sub_left_injective h)
    have hPQ : P ∪ Q ⊆ L - L := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.sub_mem_sub ht ha
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.sub_mem_sub ht hb
    have hcount := Finset.card_inter_add_card_union P Q
    have hbound := Finset.card_le_card hPQ
    have hmap : (P ∩ Q).card ≤ (L.filter fun z => z - (a - b) ∈ L).card := by
      apply Finset.card_le_card_of_injOn (fun z => z + a)
      · intro z hz
        obtain ⟨hzP, hzQ⟩ := Finset.mem_inter.mp hz
        obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp hzP
        obtain ⟨v, hv, hv_eq⟩ := Finset.mem_image.mp hzQ
        apply Finset.mem_filter.mpr
        constructor
        · simpa only [← hu_eq, sub_add_cancel] using hu
        · have heq : z + a - (a - b) = v := by
            rw [← hv_eq]
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          simpa only [heq] using hv
      · intro u _ v _ h
        exact add_right_cancel h
    omega
  have hneg {d : Γ} (hd : d ∈ L - L) : -d ∈ L - L := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hd
    simpa only [neg_sub] using Finset.sub_mem_sub hb ha
  refine ⟨{
    carrier := ↑(L - L)
    zero_mem' := ?zero
    neg_mem' := fun hd => hneg hd
    add_mem' := ?addition
  }, rfl⟩
  case zero =>
    obtain ⟨a, ha⟩ := hne
    simpa only [Finset.mem_coe, sub_self] using Finset.sub_mem_sub ha ha
  case addition =>
    intro x y hx hy
    change x + y ∈ L - L
    have hxcount := hdense x hx
    have hycount := hdense (-y) (hneg hy)
    let U := L.filter (fun z => z - x ∈ L)
    let V := L.filter (fun z => z - (-y) ∈ L)
    have hbound : (U ∪ V).card ≤ L.card :=
      Finset.card_le_card
        (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have hcount := Finset.card_inter_add_card_union U V
    have hpos : 0 < (U ∩ V).card := by
      dsimp only [U, V] at hcount hbound ⊢
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨hzU, hzV⟩ := Finset.mem_inter.mp hz
    have hzminus : z - x ∈ L := (Finset.mem_filter.mp hzU).2
    have hzplus : z + y ∈ L := by
      simpa only [sub_neg_eq_add] using (Finset.mem_filter.mp hzV).2
    have hdiff := Finset.sub_mem_sub hzplus hzminus
    have heq : (z + y) - (z - x) = x + y := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simpa only [heq] using hdiff

end D5.S3.Combinatorics.CayleyHosts.DoubleStarHostDifference
