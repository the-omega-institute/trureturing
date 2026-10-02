/- GID: D5/S3/Combinatorics/PermutationSquare/PermutationSquareCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationSquare/PermutationSquareCounting
   mirror-E: none(waiver:last-component-counting-bijection)
   anchors: []
   utility: none
   digest: Removing the final decreasing component gives the corrected counting recurrence. -/

import D5.S3.Combinatorics.PermutationSquare.PermutationSquareStructure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationSquare.PermutationSquareCounting

open D5.S3.Combinatorics Nonnesting NonnestingBasicSum
open PermutationSquareDefs PermutationSquareStructure

theorem count_recurrence (n : ℕ) (hn : 5 ≤ n) :
    a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) +
      {p : List ℕ | p ∈ avoiders n ∧ sumIndecomposable p}.ncard := by
  classical
  let assemble := FishburnTenThirteen.FishburnBasicComponents.assemble
  let decreasing (size : ℕ) := (List.range' 1 size).reverse
  let components : Set (List ℕ) := {p | p ∈ avoiders n ∧ sumIndecomposable p}
  let entries := Σ size : Fin 4, avoiders (n - (size.val + 1))
  have hlength (size : ℕ) (p : List ℕ) (hp : p ∈ avoiders size) : p.length = size := by
    simpa using hp.1.length_eq
  have hbounds (size : ℕ) (p : List ℕ) (hp : p ∈ avoiders size)
      (value : ℕ) (hv : value ∈ p) : 1 ≤ value ∧ value ≤ size := by
    have hr := hp.1.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hoffset, heq⟩ := hr
    omega
  have happend (parts rest : List (List ℕ)) :
      assemble (parts ++ rest) = directSum (assemble parts).length
        (assemble parts) (assemble rest) := by
    induction parts with
    | nil => simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble,
        directSum, shift]
    | cons block parts ih =>
      simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble, directSum,
        shift, ih, List.map_append, List.map_map, List.append_assoc, Function.comp_def,
        Nat.add_comm, Nat.add_left_comm]
  have hblock (size : ℕ) (hsize : 0 < size) (hsmall : size ≤ 4) :
      decreasing size ≠ [] ∧ decreasing size =
        (List.range' 1 (decreasing size).length).reverse ∧ (decreasing size).length ≤ 4 := by
    simp [decreasing, hsmall, Nat.ne_of_gt hsize]
  have hinsert (size : Fin 4) (p : List ℕ) (hp : p ∈ avoiders (n - (size.val + 1))) :
      directSum (n - (size.val + 1)) p (decreasing (size.val + 1)) ∈ avoiders n := by
    have hlen := hlength _ p hp
    obtain ⟨first, tail, heq, hf, hfc, _, ht⟩ :=
      avoider_layered_tail (n - (size.val + 1)) p (by omega) hp
    have hshape : assemble (first :: tail) = p := heq.symm
    have hgood := admissible_layered_tail first (tail ++ [decreasing (size.val + 1)]) hf
      hfc (by
        intro block hb
        rcases List.mem_append.mp hb with hold | hnew
        · exact ht block hold
        · simp only [List.mem_singleton] at hnew
          subst block
          exact hblock _ (by omega) (by omega))
    change assemble ((first :: tail) ++ [decreasing (size.val + 1)]) ∈
      avoiders (assemble ((first :: tail) ++ [decreasing (size.val + 1)])).length at hgood
    rw [happend, hshape] at hgood
    have hsingle : assemble [decreasing (size.val + 1)] = decreasing (size.val + 1) := by
      simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble, directSum, shift]
    rw [hsingle] at hgood
    simpa [hlen, directSum, shift, decreasing, Nat.sub_add_cancel (by omega :
      size.val + 1 ≤ n)] using hgood
  have hmaximum (size : Fin 4) (p : List ℕ) (hp : p ∈ avoiders (n - (size.val + 1))) :
      (directSum (n - (size.val + 1)) p (decreasing (size.val + 1))).getD
        (n - (size.val + 1)) 0 = n := by
    have hlen := hlength _ p hp
    change (p ++ shift (n - (size.val + 1)) (decreasing (size.val + 1))).getD
      (n - (size.val + 1)) 0 = n
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
    fin_cases size <;> simp [shift, decreasing] <;> omega
  have hprefix (size : Fin 4) (p : List ℕ) (hp : p ∈ avoiders (n - (size.val + 1)))
      (index : ℕ) (hi : index < n - (size.val + 1)) :
      (directSum (n - (size.val + 1)) p (decreasing (size.val + 1))).getD index 0 ≤
        n - (size.val + 1) := by
    have hlen := hlength _ p hp
    change (p ++ shift (n - (size.val + 1)) (decreasing (size.val + 1))).getD index 0 ≤ _
    rw [List.getD_append _ _ _ _ (by omega),
      List.getD_eq_getElem p 0 (by omega)]
    exact (hbounds _ p hp _ (List.getElem_mem (by omega))).2
  have hdecomposable (size : Fin 4) (p : List ℕ)
      (hp : p ∈ avoiders (n - (size.val + 1))) :
      ¬ sumIndecomposable (directSum (n - (size.val + 1)) p
        (decreasing (size.val + 1))) := by
    let word := directSum (n - (size.val + 1)) p (decreasing (size.val + 1))
    have hlen := hlength _ p hp
    have hwlen : word.length = n := hlength _ word (hinsert size p hp)
    intro hindecomp
    change sumIndecomposable word at hindecomp
    obtain ⟨before, after, hle⟩ := hindecomp
      ⟨n - (size.val + 1), by omega⟩ (by change 0 < n - (size.val + 1); omega)
    change (word.drop (n - (size.val + 1))).get after ≤
      (word.take (n - (size.val + 1))).get before at hle
    have ht : word.take (n - (size.val + 1)) = p := by
      simp [word, directSum, hlen]
    have hd : word.drop (n - (size.val + 1)) =
        shift (n - (size.val + 1)) (decreasing (size.val + 1)) := by
      simp [word, directSum, hlen]
    have hb : (word.take (n - (size.val + 1))).get before ∈ p := by
      rw [← ht]
      exact List.get_mem _ before
    have ha : (word.drop (n - (size.val + 1))).get after ∈
        shift (n - (size.val + 1)) (decreasing (size.val + 1)) := by
      rw [← hd]
      exact List.get_mem _ after
    have hsmall := (hbounds _ p hp _ hb).2
    obtain ⟨value, hv, heq⟩ := List.mem_map.mp ha
    have hpositive : 1 ≤ value := by
      simp only [decreasing, List.mem_reverse, List.mem_range', Nat.one_mul] at hv
      obtain ⟨offset, hoffset, heq⟩ := hv
      omega
    omega
  let build : components ⊕ entries → avoiders n := fun entry =>
    match entry with
    | Sum.inl block => ⟨block.val, block.property.1⟩
    | Sum.inr entry => ⟨directSum (n - (entry.1.val + 1)) entry.2.val
        (decreasing (entry.1.val + 1)), hinsert entry.1 entry.2.val entry.2.property⟩
  have hinjective : Function.Injective build := by
    intro left right heq
    have hval := congrArg Subtype.val heq
    cases left with
    | inl left =>
      cases right with
      | inl right =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact hval
      | inr right =>
        change left.val = directSum (n - (right.1.val + 1)) right.2.val
          (decreasing (right.1.val + 1)) at hval
        exact False.elim (hdecomposable right.1 right.2.val right.2.property
          (hval ▸ left.property.2))
    | inr left =>
      cases right with
      | inl right =>
        change directSum (n - (left.1.val + 1)) left.2.val
          (decreasing (left.1.val + 1)) = right.val at hval
        exact False.elim (hdecomposable left.1 left.2.val left.2.property
          (hval.symm ▸ right.property.2))
      | inr right =>
        change directSum (n - (left.1.val + 1)) left.2.val
          (decreasing (left.1.val + 1)) = directSum (n - (right.1.val + 1)) right.2.val
          (decreasing (right.1.val + 1)) at hval
        have hcuts : n - (left.1.val + 1) = n - (right.1.val + 1) := by
          rcases lt_trichotomy (n - (left.1.val + 1)) (n - (right.1.val + 1)) with
            hlt | hequal | hgt
          · have hmax := hmaximum left.1 left.2.val left.2.property
            have hsmall := hprefix right.1 right.2.val right.2.property _ hlt
            rw [hval] at hmax
            omega
          · exact hequal
          · have hmax := hmaximum right.1 right.2.val right.2.property
            have hsmall := hprefix left.1 left.2.val left.2.property _ hgt
            rw [← hval] at hmax
            omega
        have hsizes : left.1 = right.1 := by
          apply Fin.ext
          have hl := left.1.isLt
          have hr := right.1.isLt
          omega
        apply congrArg Sum.inr
        cases left with
        | mk size left =>
          cases right with
          | mk other right =>
            change size = other at hsizes
            subst other
            have hl := hlength _ left.val left.property
            have hr := hlength _ right.val right.property
            have ht := congrArg (List.take (n - (size.val + 1))) hval
            have hp : left.val = right.val := by
              simpa [directSum, List.take_append, hl, hr] using ht
            have : left = right := Subtype.ext hp
            subst right
            rfl
  have hsurjective : Function.Surjective build := by
    intro word
    obtain ⟨first, tail, heq, hf, hfc, hindecomp, ht⟩ :=
      avoider_layered_tail n word.val (by omega) word.property
    have hshape : assemble (first :: tail) = word.val := heq.symm
    by_cases hnil : tail = []
    · subst tail
      have hword : word.val = first := by
        simpa [directSum, shift, FishburnTenThirteen.FishburnBasicComponents.assemble] using heq
      refine ⟨Sum.inl ⟨word.val, word.property, hword.symm ▸ hindecomp⟩, ?_⟩
      rfl
    · let last := tail.getLast hnil
      let rest := tail.dropLast
      have htailshape : tail = rest ++ [last] := (List.dropLast_append_getLast hnil).symm
      have hlast := ht last (List.getLast_mem hnil)
      have hrest : ∀ block ∈ rest, block ≠ [] ∧
          block = (List.range' 1 block.length).reverse ∧ block.length ≤ 4 := by
        intro block hb
        exact ht block ((List.dropLast_sublist tail).subset hb)
      let parentWord := directSum first.length first (assemble rest)
      have hclass : parentWord ∈ avoiders parentWord.length :=
        admissible_layered_tail first rest hf hfc hrest
      have hsingle : assemble [last] = last := by
        simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble, directSum, shift]
      have hparent : assemble (first :: rest) = parentWord := rfl
      have hjoin : word.val = directSum parentWord.length parentWord last := by
        have hsum := happend (first :: rest) [last]
        rw [hparent, hsingle] at hsum
        calc
          word.val = assemble (first :: tail) := hshape.symm
          _ = assemble ((first :: rest) ++ [last]) := by rw [htailshape]; rfl
          _ = directSum parentWord.length parentWord last := hsum
      have hprefixlen : parentWord.length = n - last.length := by
        have hl := hlength _ word.val word.property
        rw [hjoin] at hl
        simp only [directSum, shift, List.length_append, List.length_map] at hl
        omega
      let size : Fin 4 := ⟨last.length - 1, by
        have hpos := List.length_pos_iff.mpr hlast.1
        omega⟩
      have hsize : size.val + 1 = last.length := by
        have hpos := List.length_pos_iff.mpr hlast.1
        dsimp [size]
        omega
      let parent : avoiders (n - (size.val + 1)) := ⟨parentWord, by
        simpa only [hsize, hprefixlen] using hclass⟩
      refine ⟨Sum.inr ⟨size, parent⟩, Subtype.ext ?_⟩
      change directSum (n - (size.val + 1)) parentWord (decreasing (size.val + 1)) = word.val
      rw [hsize, ← hprefixlen]
      change directSum parentWord.length parentWord (List.range' 1 last.length).reverse = _
      rw [← hlast.2.1]
      exact hjoin.symm
  have hfinite (size : ℕ) : (avoiders size).Finite := by
    apply (List.finite_toSet (List.range' 1 size).permutations).subset
    intro word hw
    exact List.mem_permutations.mpr hw.1
  let (size : Fin 4) : Finite (avoiders (n - (size.val + 1))) := (hfinite _).to_subtype
  let : Finite components := ((hfinite n).subset (fun _ hw => hw.1)).to_subtype
  have hcard := Nat.card_congr (Equiv.ofBijective build ⟨hinjective, hsurjective⟩)
  rw [Nat.card_sum, Nat.card_sigma] at hcard
  simp only [Nat.card_coe_set_eq] at hcard
  have hsum : (∑ size : Fin 4, (avoiders (n - (size.val + 1))).ncard) =
      a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) := by
    simp [Fin.sum_univ_succ, a]
    omega
  change components.ncard + (∑ size : Fin 4,
    (avoiders (n - (size.val + 1))).ncard) = (avoiders n).ncard at hcard
  rw [hsum] at hcard
  change (avoiders n).ncard =
    a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + components.ncard
  omega

end D5.S3.Combinatorics.PermutationSquare.PermutationSquareCounting
