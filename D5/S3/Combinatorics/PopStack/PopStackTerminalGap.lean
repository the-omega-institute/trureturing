/- GID: D5/S3/Combinatorics/PopStack/PopStackTerminalGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackTerminalGap
   mirror-E: none(waiver:terminal-minimum-gap-classification)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Two decreasing chains with one allowed internal bond determine the terminal family. -/
import D5.S3.Combinatorics.PopStack.PopStackExtra
import Mathlib.Data.List.Perm.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.PopStack.PopStackTerminalGap
open PopStackDefs PopStackChains PopStackParallel PopStackExtra
def R (size : ℕ) : List ℕ := if size % 2 = 1 then E (size / 2)
  else List.ofFn (fun index : Fin size => if index.val = 0 then size / 2
    else if index.val = 1 then size
    else if index.val % 2 = 0 then size - index.val / 2
    else size / 2 - index.val / 2)
theorem terminal_gap_classification (permutation : List ℕ) (hlength : 4 ≤ permutation.length)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hD : InD permutation) (hminimum : permutation.getD (permutation.length - 1) 0 = 1)
    (hintervals : ∀ start count lower, 2 ≤ count → count < permutation.length →
      start + count ≤ permutation.length →
      ((permutation.drop start).take count).Perm (List.range' lower count) →
      start < 2 ∧ 2 < start + count ∧ 2 ≤ lower) :
    permutation = R permutation.length := by
  classical
  let size := permutation.length; let value := fun index => permutation.getD index 0
  have hsize : 4 ≤ size := hlength; have hget : ∀ index (hindex : index < size),
      value index = permutation[index]'hindex := by
    intro index hindex; exact List.getD_eq_getElem _ _ hindex
  have hbounds : ∀ index, index < size → 1 ≤ value index ∧ value index ≤ size := by
    intro index hindex; rw [hget index hindex]
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp (List.getElem_mem hindex))
    change index < permutation.length at hindex; dsimp only [size]; omega
  have hposition : ∀ entry, 1 ≤ entry → entry ≤ size →
      ∃ index, index < size ∧ value index = entry := by
    intro entry hpositive hupper
    have hupper' : entry < 1 + permutation.length := by dsimp only [size] at hupper; omega
    obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp
      (hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hpositive, hupper'⟩))
    exact ⟨index, hindex, by rw [hget index hindex]; exact heq⟩
  have hnodup : permutation.Nodup := hperm.nodup_iff.mpr (List.nodup_range' _)
  obtain ⟨cut, hchains⟩ := (two_decreasing_chains permutation hnodup).1.mp hD
  have hchain : ∀ first second, first < second → second < size →
      (value first ≤ cut ↔ value second ≤ cut) → value second < value first := by
    intro first second horder hsecond hside
    have hh := List.pairwise_iff_getElem.mp hchains first second (by omega) hsecond horder
    rw [← hget first (by omega), ← hget second hsecond] at hh; exact hh hside
  have hgap : ∀ first second, first < second → second < size →
      (value first ≤ cut ↔ value second ≤ cut) →
      (∀ middle, first < middle → middle < second → ¬ (value middle ≤ cut ↔ value first ≤ cut)) →
      value first = value second + 1 := by
    intro first second horder hsecond hside hmiddle
    have hdecrease := hchain first second horder hsecond hside
    by_contra hnot
    obtain ⟨middle, hbound, hvalue⟩ := hposition (value second + 1)
      (by omega) (by have hh := hbounds first (by omega); omega)
    have hsideMiddle : value middle ≤ cut ↔ value first ≤ cut := by rw [hvalue]; omega
    have hleft : first < middle := by
      by_contra hh
      by_cases heq : middle = first
      · subst middle; omega
      · have hh := hchain middle first (by omega) (by omega) hsideMiddle; omega
    have hright : middle < second := by
      by_contra hh
      by_cases heq : middle = second
      · subst middle; omega
      · have hh := hchain second middle (by omega) hbound (hside.symm.trans hsideMiddle.symm); omega
    exact hmiddle middle hleft hright hsideMiddle
  have halternate : ∀ index, index + 1 < size → index ≠ 1 →
      ¬ (value index ≤ cut ↔ value (index + 1) ≤ cut) := by
    intro index hindex hnotOne hside; have hstep := hgap index (index + 1) (by omega) hindex hside
      (by
        intro middle hleft hright; omega)
    have hslice : ((permutation.drop index).take 2) = [value index, value (index + 1)] := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]; omega
      · intro position hleft hright; have hp : position = 0 ∨ position = 1 := by
          simp only [List.length_cons, List.length_nil] at hright; omega
        rcases hp with rfl | rfl
        · simp only [List.getElem_take, List.getElem_drop, Nat.add_zero]
          exact (hget index (by omega)).symm
        · simp only [List.getElem_take, List.getElem_drop]; exact (hget (index + 1) hindex).symm
    have hp : ((permutation.drop index).take 2).Perm (List.range' (value (index + 1)) 2) := by
      rw [hslice, hstep]; simpa only [List.range'_succ, List.range'_zero] using
        List.Perm.swap (value (index + 1)) (value (index + 1) + 1) []
    have hh := hintervals index 2 (value (index + 1)) (by omega) (by omega) (by omega) hp; omega
  have hfirstNotMaximum : value 0 ≠ size := by
    intro heq
    cases permutation with
    | nil => simp [size] at hsize
    | cons first tail =>
      have hfirst : first = size := by simpa only [value, List.getD_cons_zero] using heq
      have hrange : (List.range' 1 size).Perm (size :: List.range' 1 (size - 1)) := by
        have hsizeEq : size = (size - 1) + 1 := by omega
        conv_lhs => rw [hsizeEq, List.range'_1_concat]
        simpa only [show 1 + (size - 1) = size by omega] using
          List.perm_append_singleton (1 + (size - 1)) (List.range' 1 (size - 1))
      have hrest := hperm.trans hrange; rw [hfirst] at hrest
      have htail : tail.length = size - 1 := by simp [size]
      have hbad := hintervals 1 (size - 1) 1 (by omega) (by omega) (by omega)
      simp only [List.drop_succ_cons, List.drop_zero] at hbad
      rw [← htail, List.take_length] at hbad
      have hh := hbad (by simpa only [htail] using hrest.cons_inv); omega
  have hfirstLower : value 0 ≤ cut := by
    by_contra hnot
    obtain ⟨index, hindex, hmax⟩ := hposition size (by omega) (by omega)
    have hnonzero : 0 < index := by
      by_contra hh
      have hz : index = 0 := (by omega); exact hfirstNotMaximum (hz ▸ hmax)
    have hb := hbounds 0 (by omega); have hh := hchain 0 index hnonzero hindex (by omega); omega
  have hsecondUpper : cut < value 1 := by
    have hh := halternate 0 (by omega) (by omega); simp only [Nat.zero_add] at hh; omega
  have hcutBounds : 1 ≤ cut ∧ cut < size := by
    have hf := hbounds 0 (by omega); have hs := hbounds 1 (by omega); omega
  have hfirst : value 0 = cut := by
    obtain ⟨index, hindex, hcut⟩ := hposition cut hcutBounds.1 (by omega)
    by_cases hzero : index = 0
    · simpa only [hzero] using hcut
    · have hh := hchain 0 index (by omega) hindex (by omega); omega
  have hsecond : value 1 = size := by
    obtain ⟨index, hindex, hmax⟩ := hposition size (by omega) (by omega)
    have hnonzero : 0 < index := by
      by_contra hh
      have hz : index = 0 := (by omega); exact hfirstNotMaximum (hz ▸ hmax)
    by_cases hone : index = 1
    · simpa only [hone] using hmax
    · have hh := hchain 1 index (by omega) hindex (by omega); have hb := hbounds 1 (by omega); omega
  have hlast : value (size - 1) = 1 := hminimum
  by_cases hdouble : cut < value 2
  · have hparity : ∀ index, 2 ≤ index → index < size → (value index ≤ cut ↔ index % 2 = 1) := by
      intro index
      induction index using Nat.twoStepInduction with
      | zero => intro hl hb; omega
      | one => intro hl hb; omega
      | more index ih ihNext =>
        intro hl hb
        by_cases hzero : index = 0
        · subst index; change value 2 ≤ cut ↔ 2 % 2 = 1; omega
        · have hp := ihNext (by omega) (by omega)
          have ht : ¬ (value (index + 1) ≤ cut ↔ value (index + 2) ≤ cut) := by
            simpa only [Nat.add_assoc] using halternate (index + 1) (by omega) (by omega)
          omega
    have hstep : ∀ index, 2 ≤ index → index + 2 < size → value index = value (index + 2) + 1 := by
      intro index hl hb; have hp := hparity index hl (by omega)
      have hn := hparity (index + 2) (by omega) hb
      apply hgap index (index + 2) (by omega) hb (by omega); intro middle hleft hright
      have heq : middle = index + 1 := by omega
      subst middle; exact fun hh => halternate index (by omega) (by omega) hh.symm
    have hthird : value 2 = size - 1 := by
      have hh := hgap 1 2 (by omega) (by omega) (by omega) (by
          intro middle hleft hright; omega)
      omega
    have hfourth : value 3 = cut - 1 := by
      have hp := hparity 3 (by omega) (by omega)
      have hh := hgap 0 3 (by omega) (by omega) (by omega) (by
        intro middle hl hr hside
        have hm : middle = 1 ∨ middle = 2 := (by omega); rcases hm with rfl | rfl <;> omega)
      omega
    have heven : ∀ count, 1 ≤ count → 2 * count < size → value (2 * count) = size - count := by
      intro count
      induction count with
      | zero => intro hl hb; omega
      | succ count ih =>
        intro hl hb
        by_cases hz : count = 0
        · subst count; simpa using hthird
        · have hp := ih (by omega) (by omega); have hn := hstep (2 * count) (by omega) (by omega)
          have heq : 2 * (count + 1) = 2 * count + 2 := (by omega); rw [heq]; omega
    have hodd : ∀ count, 1 ≤ count → 2 * count + 1 < size →
        value (2 * count + 1) = cut - count := by
      intro count
      induction count with
      | zero => intro hl hb; omega
      | succ count ih =>
        intro hl hb
        by_cases hz : count = 0
        · subst count; simpa using hfourth
        · have hp := ih (by omega) (by omega)
          have hn := hstep (2 * count + 1) (by omega) (by omega)
          have heq : 2 * (count + 1) + 1 = (2 * count + 1) + 2 := (by omega); rw [heq]; omega
    have hsizeEven : size % 2 = 0 := by have hh := hparity (size - 1) (by omega) (by omega); omega
    have hcut : cut = size / 2 := by
      have hh := hodd (size / 2 - 1) (by omega) (by omega)
      have heq : 2 * (size / 2 - 1) + 1 = size - 1 := (by omega); rw [heq, hlast] at hh; omega
    change permutation = R size; rw [R, if_neg (by omega : ¬ size % 2 = 1)]; apply List.ext_getElem
    · simp only [List.length_ofFn]; rfl
    · intro index hp hr; rw [← hget index hp]; simp only [List.getElem_ofFn]
      by_cases hz : index = 0
      · subst index; exact hfirst.trans hcut
      · rw [if_neg hz]
        by_cases ho : index = 1
        · subst index; exact hsecond
        · rw [if_neg ho]
          by_cases he : index % 2 = 0
          · rw [if_pos he]; have hi : index = 2 * (index / 2) := by omega
            rw [hi, heven (index / 2) (by omega) (by omega)]; omega
          · rw [if_neg he]; have hi : index = 2 * (index / 2) + 1 := by omega
            rw [hi, hodd (index / 2) (by omega) (by omega), hcut]; omega
  · have hparity : ∀ index, index < size → (value index ≤ cut ↔ index % 2 = 0) := by
      intro index
      induction index with
      | zero => intro hb; simpa using hfirstLower
      | succ index ih =>
        intro hb
        by_cases hone : index = 1
        · subst index; change value 2 ≤ cut ↔ 2 % 2 = 0; omega
        · have hp := ih (by omega); have ht := halternate index (by omega) hone; omega
    have hstep : ∀ index, index + 2 < size → value index = value (index + 2) + 1 := by
      intro index hb; have hp := hparity index (by omega)
      have hn := hparity (index + 2) hb; apply hgap index (index + 2) (by omega) hb (by omega)
      intro middle hl hr; have heq : middle = index + 1 := by omega
      subst middle; have hm := hparity (index + 1) (by omega); omega
    have heven : ∀ count, 2 * count < size → value (2 * count) = cut - count := by
      intro count
      induction count with
      | zero => intro hb; simpa using hfirst
      | succ count ih =>
        intro hb; have hp := ih (by omega); have hn := hstep (2 * count) (by omega)
        have heq : 2 * (count + 1) = 2 * count + 2 := (by omega); rw [heq]; omega
    have hodd : ∀ count, 2 * count + 1 < size → value (2 * count + 1) = size - count := by
      intro count
      induction count with
      | zero => intro hb; simpa using hsecond
      | succ count ih =>
        intro hb; have hp := ih (by omega); have hn := hstep (2 * count + 1) (by omega)
        have heq : 2 * (count + 1) + 1 = (2 * count + 1) + 2 := (by omega); rw [heq]; omega
    have hsizeOdd : size % 2 = 1 := by have hh := hparity (size - 1) (by omega); omega
    have hcut : cut = size / 2 + 1 := by
      have hh := heven (size / 2) (by omega); have heq : 2 * (size / 2) = size - 1 := by omega
      rw [heq, hlast] at hh; omega
    change permutation = R size; rw [R, if_pos hsizeOdd]; apply List.ext_getElem
    · simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
        List.length_cons, List.length_nil]
      omega
    · intro index hp hr; rw [← hget index hp]
      by_cases hlastIndex : index = size - 1
      · have hi : index = (P (size / 2)).length := by simp only [P, List.length_ofFn]; omega
        simp only [E]; rw [List.getElem_append_right (by simp only [List.length_map]; omega)]
        simp only [List.length_map, ← hi, Nat.sub_self, List.getElem_cons_zero]; rw [hlastIndex]
        exact hlast
      · have hi : index < (P (size / 2)).length := by simp only [P, List.length_ofFn]; omega
        simp only [E]; rw [List.getElem_append_left (by simp only [List.length_map]; omega),
          List.getElem_map]
        simp only [P, List.getElem_ofFn]
        by_cases he : index % 2 = 0
        · rw [if_pos he]
          have heq : index = 2 * (index / 2) := (by omega); have hh := heven (index / 2) (by omega)
          rw [← heq, hcut] at hh; omega
        · rw [if_neg he]
          have heq : index = 2 * (index / 2) + 1 := by omega
          have hh := hodd (index / 2) (by omega)
          rw [← heq] at hh; omega
end D5.S3.Combinatorics.PopStack.PopStackTerminalGap
