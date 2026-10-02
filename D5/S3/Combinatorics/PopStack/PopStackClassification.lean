/- GID: D5/S3/Combinatorics/PopStack/PopStackClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackClassification
   mirror-E: none(waiver:two-chain-simple-classification)
   anchors: []
   utility: none
   digest: Every simple two-chain permutation of length at least four is alternating. -/

import D5.S3.Combinatorics.PopStack.PopStackParallel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackClassification

open PopStackDefs PopStackChains PopStackParallel

theorem simple_inD (permutation : List ℕ) (size : ℕ) (hsize : 4 ≤ size)
    (hperm : permutation.Perm (List.range' 1 size))
    (hD : InD permutation) (hsimple : IsSimple permutation) :
    ∃ half : ℕ, 2 ≤ half ∧ size = 2 * half ∧ permutation = P half := by
  have hlength : permutation.length = size := by
    simpa only [List.length_range'] using hperm.length_eq
  have hnodup : permutation.Nodup := hperm.nodup_iff.mpr (List.nodup_range' _)
  let value := fun index => permutation.getD index 0
  have hget : ∀ index (hindex : index < size),
      value index = permutation[index]'(by omega) := by
    intro index hindex
    exact List.getD_eq_getElem _ _ (by omega)
  have hbounds : ∀ index, index < size → 1 ≤ value index ∧ value index ≤ size := by
    intro index hindex
    rw [hget index hindex]
    have hh := List.mem_range'_1.mp
      (hperm.mem_iff.mp (List.getElem_mem (l := permutation) (n := index) (by omega)))
    omega
  have hposition : ∀ entry, 1 ≤ entry → entry ≤ size →
      ∃ index, index < size ∧ value index = entry := by
    intro entry hpositive hupper
    obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp
      (hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hpositive, by omega⟩))
    exact ⟨index, by omega, by rw [hget index (by omega)]; exact heq⟩
  obtain ⟨cut, hchains⟩ := (two_decreasing_chains permutation hnodup).1.mp hD
  have hchain : ∀ first second, first < second → second < size →
      (value first ≤ cut ↔ value second ≤ cut) → value second < value first := by
    intro first second horder hsecond hside
    have hh := List.pairwise_iff_getElem.mp hchains first second
      (by omega) (by omega) horder
    rw [← hget first (by omega), ← hget second hsecond] at hh
    exact hh hside
  have hgap : ∀ first second, first < second → second < size →
      (value first ≤ cut ↔ value second ≤ cut) →
      (∀ middle, first < middle → middle < second →
        ¬ (value middle ≤ cut ↔ value first ≤ cut)) →
      value first = value second + 1 := by
    intro first second horder hsecond hside hmiddle
    have hdecrease := hchain first second horder hsecond hside
    by_contra hgap
    obtain ⟨middle, hbound, hvalue⟩ := hposition (value second + 1)
      (by omega) (by have hh := hbounds first (by omega); omega)
    have hsideMiddle : value middle ≤ cut ↔ value first ≤ cut := by
      rw [hvalue]
      have hh := hside
      omega
    have hleft : first < middle := by
      by_contra hnot
      by_cases heq : middle = first
      · subst middle
        omega
      · have hh := hchain middle first (by omega) (by omega) hsideMiddle
        omega
    have hright : middle < second := by
      by_contra hnot
      by_cases heq : middle = second
      · subst middle
        omega
      · have hh := hchain second middle (by omega) hbound
          (hside.symm.trans hsideMiddle.symm)
        omega
    exact hmiddle middle hleft hright hsideMiddle
  have halternate : ∀ index, index + 1 < size →
      ¬ (value index ≤ cut ↔ value (index + 1) ≤ cut) := by
    intro index hindex hside
    have hstep := hgap index (index + 1) (by omega) hindex hside
      (by intro middle hleft hright; omega)
    have hslice : ((permutation.drop index).take 2) = [value index, value (index + 1)] := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]
        omega
      · intro position hleft hright
        have hposition : position = 0 ∨ position = 1 := by
          simp only [List.length_cons, List.length_nil] at hright
          omega
        rcases hposition with rfl | rfl
        · simp only [List.getElem_take, List.getElem_drop, Nat.add_zero]
          simpa using (hget index (by omega)).symm
        · simp only [List.getElem_take, List.getElem_drop]
          simpa using (hget (index + 1) hindex).symm
    apply hsimple index 2 (value (index + 1)) (by omega) (by omega) (by omega)
    rw [hslice, hstep]
    simpa only [List.range'_succ, List.range'_zero, List.append_nil] using
      List.Perm.swap (value (index + 1)) (value (index + 1) + 1) []
  have hfirstNotMaximum : value 0 ≠ size := by
    intro heq
    cases permutation with
    | nil => simp at hlength; omega
    | cons first tail =>
      have hfirst : first = size := by simpa only [value, List.getD_cons_zero] using heq
      have hrange : (List.range' 1 size).Perm (size :: List.range' 1 (size - 1)) := by
        have hsizeEq : size = (size - 1) + 1 := by omega
        conv_lhs => rw [hsizeEq, List.range'_1_concat]
        have hh : 1 + (size - 1) = size := by omega
        simpa only [hh] using
          List.perm_append_singleton (1 + (size - 1)) (List.range' 1 (size - 1))
      have hrest := hperm.trans hrange
      rw [hfirst] at hrest
      have hbad := hsimple 1 (size - 1) 1 (by omega) (by omega) (by omega)
      simp only [List.drop_succ_cons, List.drop_zero] at hbad
      have htail : tail.length = size - 1 := by simp only [List.length_cons] at hlength; omega
      rw [← htail, List.take_length] at hbad
      exact hbad (by simpa only [htail] using hrest.cons_inv)
  have hlastNotMinimum : value (size - 1) ≠ 1 := by
    intro heq
    have hlast : permutation.drop (size - 1) = [value (size - 1)] := by
      apply List.ext_getElem
      · simp only [List.length_drop, List.length_cons, List.length_nil]
        omega
      · intro index hleft hright
        have hzero : index = 0 := by
          simp only [List.length_cons, List.length_nil] at hright
          omega
        subst index
        simp only [List.getElem_drop, Nat.add_zero]
        simpa using (hget (size - 1) (by omega)).symm
    have hdecompose : permutation = permutation.take (size - 1) ++ [1] := by
      calc
        permutation = permutation.take (size - 1) ++ permutation.drop (size - 1) :=
          (List.take_append_drop (size - 1) permutation).symm
        _ = _ := by rw [hlast, heq]
    have hrest : (permutation.take (size - 1)).Perm (List.range' 2 (size - 1)) := by
      have hrange : List.range' 1 size = 1 :: List.range' 2 (size - 1) := by
        have hh : size = (size - 1) + 1 := by omega
        conv_lhs => rw [hh, List.range'_succ]
      have hp := hperm
      conv_lhs at hp => rw [hdecompose]
      rw [hrange] at hp
      have hh := (List.perm_append_singleton 1 (permutation.take (size - 1))).symm.trans
        hp
      exact hh.cons_inv
    apply hsimple 0 (size - 1) 2 (by omega) (by omega) (by omega)
    simpa only [List.drop_zero] using hrest
  have hfirstLower : value 0 ≤ cut := by
    by_contra hnot
    obtain ⟨index, hindex, hmax⟩ := hposition size (by omega) (by omega)
    have hfirstBounds := hbounds 0 (by omega)
    have hnonzero : 0 < index := by
      by_contra hh
      have hz : index = 0 := by omega
      exact hfirstNotMaximum (hz ▸ hmax)
    have hbad := hchain 0 index hnonzero hindex (by omega)
    omega
  have hlastUpper : cut < value (size - 1) := by
    by_contra hnot
    obtain ⟨index, hindex, hmin⟩ := hposition 1 (by omega) (by omega)
    have hlastBounds := hbounds (size - 1) (by omega)
    have hbefore : index < size - 1 := by
      by_contra hh
      have heq : index = size - 1 := by omega
      exact hlastNotMinimum (heq ▸ hmin)
    have hbad := hchain index (size - 1) hbefore (by omega) (by omega)
    omega
  have hparity : ∀ index, index < size → (value index ≤ cut ↔ index % 2 = 0) := by
    intro index
    induction index with
    | zero => intro hindex; simpa using hfirstLower
    | succ index ih =>
      intro hindex
      have hprevious := ih (by omega)
      have htoggled := halternate index (by omega)
      omega
  have hcutBounds : 1 ≤ cut ∧ cut < size := by
    have hh := hbounds 0 (by omega)
    have ht := hbounds (size - 1) (by omega)
    omega
  have hfirst : value 0 = cut := by
    obtain ⟨index, hindex, hcut⟩ := hposition cut hcutBounds.1 (by omega)
    by_cases hzero : index = 0
    · simpa only [hzero] using hcut
    · have hh := hchain 0 index (by omega) hindex (by omega)
      omega
  have hsecond : value 1 = size := by
    obtain ⟨index, hindex, hmax⟩ := hposition size (by omega) (by omega)
    have hsecondUpper : cut < value 1 := by have hh := hparity 1 (by omega); omega
    have hindexPositive : 0 < index := by
      by_contra hh
      have hz : index = 0 := by omega
      rw [hz] at hmax
      omega
    by_cases hone : index = 1
    · simpa only [hone] using hmax
    · have hh := hchain 1 index (by omega) hindex (by omega)
      have hb := hbounds 1 (by omega)
      omega
  have hlast : value (size - 1) = cut + 1 := by
    obtain ⟨index, hindex, hcut⟩ := hposition (cut + 1) (by omega) (by omega)
    by_cases heq : index = size - 1
    · simpa only [heq] using hcut
    · have hh := hchain index (size - 1) (by omega) (by omega) (by omega)
      omega
  have hstep : ∀ index, index + 2 < size → value index = value (index + 2) + 1 := by
    intro index hindex
    have hfirstSide := hparity index (by omega)
    have hsecondSide := hparity (index + 2) hindex
    apply hgap index (index + 2) (by omega) hindex (by omega)
    intro middle hleft hright
    have heq : middle = index + 1 := by omega
    subst middle
    exact fun hh => halternate index (by omega) hh.symm
  have heven : ∀ count, 2 * count < size → value (2 * count) = cut - count := by
    intro count
    induction count with
    | zero => intro hcount; simpa using hfirst
    | succ count ih =>
      intro hcount
      have hprevious := ih (by omega)
      have hnext := hstep (2 * count) (by omega)
      have hindexEq : 2 * (count + 1) = 2 * count + 2 := by omega
      rw [hindexEq] at hcount ⊢
      omega
  have hodd : ∀ count, 2 * count + 1 < size → value (2 * count + 1) = size - count := by
    intro count
    induction count with
    | zero => intro hcount; simpa using hsecond
    | succ count ih =>
      intro hcount
      have hprevious := ih (by omega)
      have hnext := hstep (2 * count + 1) (by omega)
      have hindexEq : 2 * (count + 1) + 1 = (2 * count + 1) + 2 := by omega
      rw [hindexEq] at hcount ⊢
      omega
  have hsizeEven : size = 2 * (size / 2) := by
    have hh := hparity (size - 1) (by omega)
    omega
  let half := size / 2
  have hhalf : 2 ≤ half := by dsimp [half]; omega
  have hsizeHalf : size = 2 * half := hsizeEven
  have hcutHalf : cut = half := by
    have hh := hodd (half - 1) (by omega)
    have heq : 2 * (half - 1) + 1 = size - 1 := by omega
    rw [heq, hlast] at hh
    omega
  refine ⟨half, hhalf, hsizeHalf, ?_⟩
  apply List.ext_getElem
  · simp only [P, List.length_ofFn, hlength, hsizeHalf]
  · intro index hindex hPindex
    have hbound : index < size := by omega
    rw [← hget index hbound]
    simp only [P, List.getElem_ofFn]
    by_cases heq : index % 2 = 0
    · rw [if_pos heq]
      have hindexEq : index = 2 * (index / 2) := by omega
      rw [hindexEq, heven (index / 2) (by omega), hcutHalf]
      omega
    · rw [if_neg heq]
      have hindexEq : index = 2 * (index / 2) + 1 := by omega
      rw [hindexEq, hodd (index / 2) (by omega), hsizeHalf]
      omega

end D5.S3.Combinatorics.PopStack.PopStackClassification
