/- GID: D5/S3/Combinatorics/PopStack/PopStackPrefixShape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackPrefixShape
   mirror-E: none(waiver:prefix-only-two-chain-shape)
   anchors: []
   utility: none
   digest: Prefix-only two-chain permutations without a terminal minimum have one initial bond. -/

import D5.S3.Combinatorics.PopStack.PopStackParallel
import D5.S3.Combinatorics.PopStack.PopStackClassification
import D5.S3.Combinatorics.PopStack.PopStackInflation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackPrefixShape

open PopStackDefs PopStackChains PopStackParallel PopStackInflation

theorem prefix_nonterminal (permutation : List ℕ) (size : ℕ) (hsize : 3 ≤ size)
    (hperm : permutation.Perm (List.range' 1 size)) (hD : InD permutation)
    (hprefix : ∀ start count lower, 2 ≤ count → count < size → start + count ≤ size →
      ((permutation.drop start).take count).Perm (List.range' lower count) → start = 0)
    (hlastNotMinimum : permutation.getD (size - 1) 0 ≠ 1) :
    ∃ half : ℕ, 1 ≤ half ∧
      ((size = 2 * half ∧ permutation = P half) ∨
        (size = 2 * half + 1 ∧ permutation = inflate (P half) 0 [2, 1])) := by
  by_cases hprime : 4 ≤ size ∧ IsSimple permutation
  · obtain ⟨half, hhalf, hsizeHalf, hshape⟩ :=
      PopStackClassification.simple_inD permutation size hprime.1 hperm hD hprime.2
    exact ⟨half, by omega, Or.inl ⟨hsizeHalf, hshape⟩⟩
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
  have halternate : ∀ index, 1 ≤ index → index + 1 < size →
      ¬ (value index ≤ cut ↔ value (index + 1) ≤ cut) := by
    intro index hpositive hindex hside
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
    have hinterval : ((permutation.drop index).take 2).Perm
        (List.range' (value (index + 1)) 2) := by
      rw [hslice, hstep]
      simpa only [List.range'_succ, List.range'_zero, List.append_nil] using
        List.Perm.swap (value (index + 1)) (value (index + 1) + 1) []
    have hh := hprefix index 2 (value (index + 1)) (by omega) (by omega) (by omega) hinterval
    omega
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
      have htail : tail.length = size - 1 := by simp only [List.length_cons] at hlength; omega
      have hinterval : (((first :: tail).drop 1).take (size - 1)).Perm
          (List.range' 1 (size - 1)) := by
        simp only [List.drop_succ_cons, List.drop_zero]
        rw [← htail, List.take_length]
        simpa only [htail] using hrest.cons_inv
      have hh := hprefix 1 (size - 1) 1 (by omega) (by omega) (by omega) hinterval
      omega
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
  let extra : ℕ := if value 1 ≤ cut then 1 else 0
  have hextra : extra = 0 ∨ extra = 1 := by dsimp [extra]; split_ifs <;> simp
  have hstartLower : value extra ≤ cut := by
    dsimp only [extra]
    split_ifs with hside
    · exact hside
    · exact hfirstLower
  have hstart : value extra = cut - extra := by
    dsimp only [extra]
    split_ifs with hside
    · have hh := hgap 0 1 (by omega) (by omega) (by omega)
        (by intro middle hleft hright; omega)
      omega
    · omega
  have htoggled : ∀ index, extra + index + 1 < size →
      ¬ (value (extra + index) ≤ cut ↔ value (extra + index + 1) ≤ cut) := by
    intro index hindex
    by_cases hpositive : 1 ≤ extra + index
    · exact halternate (extra + index) hpositive hindex
    · have hz : extra = 0 := by omega
      have hi : index = 0 := by omega
      have hside : ¬ value 1 ≤ cut := by
        intro hh
        dsimp only [extra] at hz
        rw [if_pos hh] at hz
        omega
      rw [hz, hi]
      simpa using (show ¬ (value 0 ≤ cut ↔ value 1 ≤ cut) by omega)
  have hparity : ∀ index, extra + index < size →
      (value (extra + index) ≤ cut ↔ index % 2 = 0) := by
    intro index
    induction index with
    | zero => intro hindex; simpa using hstartLower
    | succ index ih =>
      intro hindex
      have hprevious := ih (by omega)
      have hnext := htoggled index (by omega)
      have heq : extra + (index + 1) = extra + index + 1 := by omega
      rw [heq]
      omega
  have hsecond : value (extra + 1) = size := by
    obtain ⟨index, hindex, hmax⟩ := hposition size (by omega) (by omega)
    have hupper : cut < value (extra + 1) := by have hh := hparity 1 (by omega); omega
    have hafter : extra + 1 ≤ index := by
      by_contra hh
      have heq : index = 0 ∨ index = extra := by omega
      rcases heq with rfl | rfl <;> omega
    by_cases heq : index = extra + 1
    · simpa only [heq] using hmax
    · have hh := hchain (extra + 1) index (by omega) hindex (by omega)
      have hb := hbounds (extra + 1) (by omega)
      omega
  have hlast : value (size - 1) = cut + 1 := by
    obtain ⟨index, hindex, hcut⟩ := hposition (cut + 1) (by omega) (by omega)
    by_cases heq : index = size - 1
    · simpa only [heq] using hcut
    · have hh := hchain index (size - 1) (by omega) (by omega) (by omega)
      omega
  have hstep : ∀ index, extra + index + 2 < size →
      value (extra + index) = value (extra + index + 2) + 1 := by
    intro index hindex
    have hfirstSide := hparity index (by omega)
    have hsecondSide := hparity (index + 2) (by omega)
    have heq : extra + (index + 2) = extra + index + 2 := by omega
    rw [heq] at hsecondSide
    apply hgap (extra + index) (extra + index + 2) (by omega) hindex (by omega)
    intro middle hleft hright
    have hm : middle = extra + index + 1 := by omega
    subst middle
    exact fun hh => htoggled index (by omega) hh.symm
  have heven : ∀ count, extra + 2 * count < size →
      value (extra + 2 * count) = cut - extra - count := by
    intro count
    induction count with
    | zero => intro hcount; simpa using hstart
    | succ count ih =>
      intro hcount
      have hprevious := ih (by omega)
      have hnext := hstep (2 * count) (by omega)
      have heq : extra + 2 * (count + 1) = extra + 2 * count + 2 := by omega
      rw [heq] at hcount ⊢
      omega
  have hodd : ∀ count, extra + 2 * count + 1 < size →
      value (extra + 2 * count + 1) = size - count := by
    intro count
    induction count with
    | zero => intro hcount; simpa using hsecond
    | succ count ih =>
      intro hcount
      have hprevious := ih (by omega)
      have hnext := hstep (2 * count + 1) (by omega)
      have heq : extra + 2 * (count + 1) + 1 = extra + (2 * count + 1) + 2 := by omega
      rw [heq] at hcount ⊢
      simp only [Nat.add_assoc, Nat.reduceAdd] at hprevious hnext ⊢
      omega
  let half := (size - extra) / 2
  have hsizeHalf : size = 2 * half + extra := by
    have hh := hparity (size - 1 - extra) (by omega)
    have heq : extra + (size - 1 - extra) = size - 1 := by omega
    rw [heq] at hh
    dsimp [half]
    omega
  have hhalf : 1 ≤ half := by omega
  have hcutHalf : cut = half + extra := by
    have hh := hodd (half - 1) (by omega)
    have heq : extra + 2 * (half - 1) + 1 = size - 1 := by omega
    rw [heq, hlast] at hh
    omega
  refine ⟨half, hhalf, ?_⟩
  rcases hextra with hzero | hone
  · left
    refine ⟨by omega, ?_⟩
    apply List.ext_getElem
    · simp only [P, List.length_ofFn, hlength]
      omega
    · intro index hindex hPindex
      have hbound : index < size := by omega
      rw [← hget index hbound]
      simp only [P, List.getElem_ofFn]
      by_cases heq : index % 2 = 0
      · rw [if_pos heq]
        have hi : index = extra + 2 * (index / 2) := by omega
        rw [hi, heven (index / 2) (by omega), hcutHalf, hzero]
        omega
      · rw [if_neg heq]
        have hi : index = extra + 2 * (index / 2) + 1 := by omega
        rw [hi, hodd (index / 2) (by omega), hsizeHalf, hzero]
        omega
  · right
    have hPlength : (P half).length = 2 * half := List.length_ofFn
    have hPfirst : (P half).getD 0 0 = half := by
      rw [List.getD_eq_getElem _ _ (by simp only [P, List.length_ofFn]; omega)]
      simp only [P, List.getElem_ofFn, Nat.zero_mod, Nat.zero_div, ite_true, Nat.sub_zero]
    let shift := fun entry => if half < entry then entry + 1 else entry
    have hinflate : inflate (P half) 0 [2, 1] =
        (half + 1) :: half :: ((P half).drop 1).map shift := by
      dsimp only [inflate]
      rw [hPfirst]
      simp [shift]
    refine ⟨by omega, ?_⟩
    apply List.ext_getElem
    · rw [hinflate]
      simp only [List.length_cons, List.length_map, List.length_drop, P,
        List.length_ofFn, hlength]
      omega
    · intro index hindex hQindex
      have hbound : index < size := by omega
      rw [← hget index hbound]
      rw [← List.getD_eq_getElem _ 0 hQindex, hinflate]
      by_cases hfirstIndex : index = 0
      · subst index
        simpa only [List.getD_cons_zero, hone] using hfirst.trans hcutHalf
      by_cases hsecondIndex : index = 1
      · subst index
        have hh := hstart
        rw [hone, hcutHalf, hone] at hh
        simpa only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_cancel] using hh
      have hi : index = (index - 2) + 2 := by omega
      conv_rhs => rw [hi]
      simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem _ 0 (by
        simp only [List.length_map, List.length_drop, hPlength]; omega)]
      simp only [List.getElem_map, List.getElem_drop]
      have hpositionEq : 1 + (index - 2) = index - 1 := by omega
      simp only [hpositionEq]
      simp only [P, List.getElem_ofFn, shift]
      by_cases hoddIndex : index % 2 = 1
      · have hPparity : (index - 1) % 2 = 0 := by omega
        rw [if_pos hPparity, if_neg (by omega)]
        have hindexEq : index = extra + 2 * (index / 2) := by omega
        rw [hindexEq, heven (index / 2) (by omega), hcutHalf, hone]
        omega
      · have hPparity : (index - 1) % 2 ≠ 0 := by omega
        rw [if_neg hPparity, if_pos (by omega)]
        have hindexEq : index = extra + 2 * ((index - 1) / 2) + 1 := by omega
        rw [hindexEq, hodd ((index - 1) / 2) (by omega), hsizeHalf, hone]
        omega

end D5.S3.Combinatorics.PopStack.PopStackPrefixShape
