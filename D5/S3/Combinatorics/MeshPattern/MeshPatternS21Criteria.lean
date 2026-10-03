/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Criteria
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Criteria
   mirror-E: none(waiver:elementary-mesh-occurrence-criterion)
   anchors: [mathlib/module/Mathlib.Data.List.GetD, mathlib/module/Mathlib.Data.List.Nodup]
   utility: none
   digest: Mesh occurrences are unique anchored rectangles in a staircase Ferrers region. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21

open MeshPatternS21Defs

def rectangle (p : List ℕ) (width height : ℕ) : Finset ℕ :=
  (Finset.range width).filter (fun position => p.getD position 0 ≤ height)

theorem shading_criterion (p : List ℕ) (hp : p.Nodup) (first middle last : ℕ)
    (hfirst : first < middle) (hmiddle : middle < last) (hlast : last < p.length) :
    (∀ position < p.length, position ≠ first → position ≠ middle → position ≠ last →
      ¬ Shaded (column first middle last position)
        (row (p.getD first 0) (p.getD middle 0) (p.getD last 0)
          (p.getD position 0))) ↔
    (∀ position < p.length, position ≠ first → position ≠ middle → position ≠ last →
      (position < last →
        max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) <
          p.getD position 0) ∧
      (last < position →
        p.getD position 0 <
          max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0))) := by
  have hindex : ∀ left right, left < p.length → right < p.length →
      p.getD left 0 = p.getD right 0 → left = right := by
    intro left right hleft hright heq
    rw [List.getD_eq_getElem p 0 hleft, List.getD_eq_getElem p 0 hright] at heq
    exact hp.getElem_inj_iff.mp heq
  have hlocal : ∀ position < p.length, position ≠ first → position ≠ middle →
      position ≠ last →
      ((¬ Shaded (column first middle last position)
        (row (p.getD first 0) (p.getD middle 0) (p.getD last 0)
          (p.getD position 0))) ↔
      ((position < last →
        max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) <
          p.getD position 0) ∧
      (last < position →
        p.getD position 0 <
          max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)))) := by
    intro position hposition hnefirst hnemiddle hnelast
    have hvaluefirst : p.getD position 0 ≠ p.getD first 0 :=
      fun heq => hnefirst (hindex position first hposition (by omega) heq)
    have hvaluemiddle : p.getD position 0 ≠ p.getD middle 0 :=
      fun heq => hnemiddle (hindex position middle hposition (by omega) heq)
    have hvaluelast : p.getD position 0 ≠ p.getD last 0 :=
      fun heq => hnelast (hindex position last hposition hlast heq)
    simp only [Shaded, column, row]
    split_ifs <;> omega
  constructor
  · intro hshade position hposition hnefirst hnemiddle hnelast
    exact (hlocal position hposition hnefirst hnemiddle hnelast).mp
      (hshade position hposition hnefirst hnemiddle hnelast)
  · intro hsep position hposition hnefirst hnemiddle hnelast
    exact (hlocal position hposition hnefirst hnemiddle hnelast).mpr
      (hsep position hposition hnefirst hnemiddle hnelast)

theorem rectangle_criterion (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
    (∀ (inc : Bool) (first middle last : ℕ),
      IsOccurrence inc p (first, middle, last) ↔
      first < middle ∧ middle < last ∧ last < p.length ∧
        (if inc then p.getD first 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD last 0
          else p.getD last 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD first 0) ∧
        rectangle p (last + 1)
          (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)) =
            {first, middle, last} ∧
        last + 1 + max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) = n + 3) ∧
    (∀ (inc otherInc : Bool) (left right : ℕ × ℕ × ℕ),
      IsOccurrence inc p left → IsOccurrence otherInc p right →
      max (max (p.getD left.1 0) (p.getD left.2.1 0)) (p.getD left.2.2 0) =
        max (max (p.getD right.1 0) (p.getD right.2.1 0)) (p.getD right.2.2 0) →
      left = right) ∧
    (∀ (inc otherInc : Bool) (left right : ℕ × ℕ × ℕ),
      IsOccurrence inc p left → IsOccurrence otherInc p right →
      left.2.2 = right.2.2 → left = right) ∧
    (∀ inc : Bool, occ inc p =
      {maximum | ∃ first middle last,
        first < middle ∧ middle < last ∧ last < p.length ∧
        (if inc then p.getD first 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD last 0
          else p.getD last 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD first 0) ∧
        max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) = maximum ∧
        rectangle p (n - maximum + 3) maximum = {first, middle, last} ∧
        last + 1 = n - maximum + 3}.ncard) := by
  have hcriterion : ∀ (inc : Bool) (first middle last : ℕ),
      IsOccurrence inc p (first, middle, last) ↔
      first < middle ∧ middle < last ∧ last < p.length ∧
        (if inc then p.getD first 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD last 0
          else p.getD last 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD first 0) ∧
        rectangle p (last + 1)
          (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)) =
            {first, middle, last} ∧
        last + 1 + max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) = n + 3 := by
    intro inc first middle last
    classical
    have hlength : p.length = n := by simpa using hp.length_eq
    have hnodup : p.Nodup := hp.nodup_iff.mpr (List.nodup_range')
    have hindex : ∀ left right, left < n → right < n →
        p.getD left 0 = p.getD right 0 → left = right := by
      intro left right hleft hright heq
      rw [List.getD_eq_getElem p 0 (by omega),
        List.getD_eq_getElem p 0 (by omega)] at heq
      exact hnodup.getElem_inj_iff.mp heq
    have hvalues : ∀ position < n, 1 ≤ p.getD position 0 ∧ p.getD position 0 ≤ n := by
      intro position hposition
      have hmem := hp.mem_iff.mp (List.getElem_mem (l := p) (n := position) (by omega))
      rw [List.mem_range'_1] at hmem
      rw [List.getD_eq_getElem p 0 (by omega)]
      omega
    suffices ∀ (hfirst : first < middle) (hmiddle : middle < last)
        (hlast : last < p.length),
        (∀ position < p.length, position ≠ first → position ≠ middle →
          position ≠ last →
          ¬ Shaded (column first middle last position)
            (row (p.getD first 0) (p.getD middle 0) (p.getD last 0)
              (p.getD position 0))) ↔
        (rectangle p (last + 1)
          (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)) =
            {first, middle, last} ∧
        last + 1 + max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) = n + 3) by
      simp only [IsOccurrence]
      constructor
      · rintro ⟨hfirst, hmiddle, hlast, horder, hshade⟩
        exact ⟨hfirst, hmiddle, hlast, horder, (this hfirst hmiddle hlast).mp hshade⟩
      · rintro ⟨hfirst, hmiddle, hlast, horder, hrect⟩
        exact ⟨hfirst, hmiddle, hlast, horder, (this hfirst hmiddle hlast).mpr hrect⟩
    intro hfirst hmiddle hlast
    let maximum := max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)
    let selected : Finset ℕ := {first, middle, last}
    let low := rectangle p n maximum
    let prefixPoints := rectangle p (last + 1) maximum
    let suffix := Finset.range n \ Finset.range (last + 1)
    have hmaximum : 1 ≤ maximum ∧ maximum ≤ n := by
      have := hvalues first (by omega)
      have := hvalues middle (by omega)
      have := hvalues last (by omega)
      dsimp [maximum]
      omega
    have hselected : selected.card = 3 := by
      simp [selected, Finset.card_insert_of_notMem, ne_of_lt hfirst,
        ne_of_lt hmiddle, ne_of_lt (lt_trans hfirst hmiddle)]
    have hprefixsub : prefixPoints ⊆ low := by
      intro position hposition
      simp only [prefixPoints, low, rectangle, Finset.mem_filter, Finset.mem_range] at *
      exact ⟨by omega, hposition.2⟩
    have hselectedsub : selected ⊆ prefixPoints := by
      intro position hposition
      simp only [selected, Finset.mem_insert, Finset.mem_singleton] at hposition
      simp only [prefixPoints, rectangle, Finset.mem_filter, Finset.mem_range, maximum]
      rcases hposition with rfl | rfl | rfl <;> constructor <;> omega
    have hlowcard : low.card = maximum := by
      have himage : low.image (fun position => p.getD position 0) =
          (Finset.range (maximum + 1)).erase 0 := by
        ext value
        simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range]
        constructor
        · rintro ⟨position, hposition, rfl⟩
          have hbound : position < n ∧ p.getD position 0 ≤ maximum := by
            simpa [low, rectangle] using hposition
          have := hvalues position hbound.1
          omega
        · rintro ⟨hne, hbound⟩
          have hmem : value ∈ p := hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          obtain ⟨position, hposition, hvalue⟩ := List.mem_iff_getElem.mp hmem
          refine ⟨position, ?_, ?_⟩
          · simp only [low, rectangle, Finset.mem_filter, Finset.mem_range]
            rw [List.getD_eq_getElem p 0 hposition, hvalue]
            exact ⟨by omega, by omega⟩
          · exact (List.getD_eq_getElem p 0 hposition).trans hvalue
      have hinjective : Set.InjOn (fun position => p.getD position 0) low := by
        intro left hleft right hright heq
        have hleftbound : left < n := (Finset.mem_filter.mp hleft).1 |> Finset.mem_range.mp
        have hrightbound : right < n :=
          (Finset.mem_filter.mp hright).1 |> Finset.mem_range.mp
        exact hindex left right hleftbound hrightbound heq
      have hcard := Finset.card_image_of_injOn hinjective
      rw [himage, Finset.card_erase_of_mem (by simp), Finset.card_range] at hcard
      omega
    have hsuffixcard : suffix.card = n - (last + 1) := by
      simpa [suffix] using
        Finset.card_sdiff_of_subset (Finset.range_mono (show last + 1 ≤ n by omega))
    have hthree : 3 ≤ maximum := by
      have hcard := Finset.card_le_card (hselectedsub.trans hprefixsub)
      simpa only [hselected, hlowcard] using hcard
    have hlowdiffsub : low \ prefixPoints ⊆ suffix := by
      intro position hposition
      simp only [low, prefixPoints, suffix, rectangle, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_range] at *
      exact ⟨hposition.1.1, by omega⟩
    rw [shading_criterion p hnodup first middle last hfirst hmiddle hlast]
    constructor
    · intro hsep
      have hrect : prefixPoints = selected := by
        apply Finset.Subset.antisymm _ hselectedsub
        intro position hposition
        have hbound : position < last + 1 ∧ p.getD position 0 ≤ maximum := by
          simpa [prefixPoints, rectangle] using hposition
        simp only [selected, Finset.mem_insert, Finset.mem_singleton]
        by_contra hnot
        push Not at hnot
        have hlarge := (hsep position (by omega) hnot.1 hnot.2.1 hnot.2.2).1 (by omega)
        omega
      have hdiff : low \ prefixPoints = suffix := by
        apply Finset.Subset.antisymm hlowdiffsub
        intro position hposition
        have hbound : position < n ∧ ¬position < last + 1 := by
          simpa [suffix] using hposition
        have hsmall := (hsep position (by omega) (by omega) (by omega) (by omega)).2
          (by omega)
        simp only [low, prefixPoints, rectangle, Finset.mem_sdiff, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨⟨hbound.1, by omega⟩, by omega⟩
      have hcard := Finset.card_sdiff_of_subset hprefixsub
      rw [hdiff, hrect, hselected, hlowcard, hsuffixcard] at hcard
      exact ⟨hrect, by dsimp [maximum] at *; omega⟩
    · rintro ⟨hrect, hsum⟩
      change prefixPoints = selected at hrect
      have hdiff : low \ prefixPoints = suffix := by
        apply Finset.eq_of_subset_of_card_le hlowdiffsub
        have hprefixcard : prefixPoints.card = 3 := hrect ▸ hselected
        have hcard := Finset.card_sdiff_of_subset hprefixsub
        rw [hprefixcard, hlowcard] at hcard
        rw [hcard, hsuffixcard]
        dsimp [maximum] at *
        omega
      intro position hposition hnefirst hnemiddle hnelast
      constructor
      · intro hbefore
        have hnot : position ∉ prefixPoints := by
          rw [hrect]
          simp [selected, hnefirst, hnemiddle, hnelast]
        simp only [prefixPoints, rectangle, Finset.mem_filter, Finset.mem_range] at hnot
        change maximum < p.getD position 0
        omega
      · intro hafter
        have hsuffix : position ∈ suffix := by
          simp only [suffix, Finset.mem_sdiff, Finset.mem_range]
          exact ⟨by omega, by omega⟩
        rw [← hdiff] at hsuffix
        have hsmall : p.getD position 0 ≤ maximum := (Finset.mem_filter.mp
          (Finset.mem_sdiff.mp hsuffix).1).2
        have hne : p.getD position 0 ≠ maximum := by
          intro heq
          dsimp [maximum] at heq
          have heqfirst := hindex position first (by omega) (by omega)
          have heqmiddle := hindex position middle (by omega) (by omega)
          have heqlast := hindex position last (by omega) (by omega)
          omega
        change p.getD position 0 < maximum
        omega
  have hsorted : ∀ (first middle last otherFirst otherMiddle otherLast : ℕ),
      first < middle → middle < last → otherFirst < otherMiddle → otherMiddle < otherLast →
      ({first, middle, last} : Finset ℕ) = {otherFirst, otherMiddle, otherLast} →
      (first, middle, last) = (otherFirst, otherMiddle, otherLast) := by
    intro first middle last otherFirst otherMiddle otherLast
      hfirst hmiddle hotherFirst hotherMiddle heq
    have hforward : ∀ position, position = first ∨ position = middle ∨ position = last →
        position = otherFirst ∨ position = otherMiddle ∨ position = otherLast := by
      intro position hposition
      have hmem : position ∈ ({first, middle, last} : Finset ℕ) := by simpa using hposition
      rw [heq] at hmem
      simpa using hmem
    have hbackward : ∀ position,
        position = otherFirst ∨ position = otherMiddle ∨ position = otherLast →
        position = first ∨ position = middle ∨ position = last := by
      intro position hposition
      have hmem : position ∈ ({otherFirst, otherMiddle, otherLast} : Finset ℕ) := by
        simpa using hposition
      rw [← heq] at hmem
      simpa using hmem
    have := hforward first (by simp)
    have := hforward middle (by simp)
    have := hforward last (by simp)
    have := hbackward otherFirst (by simp)
    have := hbackward otherMiddle (by simp)
    have := hbackward otherLast (by simp)
    have heqFirst : first = otherFirst := by omega
    have heqMiddle : middle = otherMiddle := by omega
    have heqLast : last = otherLast := by omega
    exact Prod.ext heqFirst (Prod.ext heqMiddle heqLast)
  have hlastUnique : ∀ (inc otherInc : Bool) (left right : ℕ × ℕ × ℕ),
      IsOccurrence inc p left → IsOccurrence otherInc p right →
      left.2.2 = right.2.2 → left = right := by
    intro inc otherInc left right hleft hright hlast
    rcases left with ⟨first, middle, last⟩
    rcases right with ⟨otherFirst, otherMiddle, otherLast⟩
    change last = otherLast at hlast
    subst otherLast
    obtain ⟨hfirst, hmiddle, _, _, hrect, _⟩ :=
      (hcriterion inc first middle last).mp hleft
    obtain ⟨hotherFirst, hotherMiddle, _, _, hotherRect, _⟩ :=
      (hcriterion otherInc otherFirst otherMiddle last).mp hright
    have hcard : ({first, middle, last} : Finset ℕ).card =
        ({otherFirst, otherMiddle, last} : Finset ℕ).card := by
      simp [Finset.card_insert_of_notMem, ne_of_lt hfirst, ne_of_lt hmiddle,
        ne_of_lt (lt_trans hfirst hmiddle), ne_of_lt hotherFirst, ne_of_lt hotherMiddle,
        ne_of_lt (lt_trans hotherFirst hotherMiddle)]
    have hsubset : ∀ (lowHeight highHeight : ℕ), lowHeight ≤ highHeight →
        rectangle p (last + 1) lowHeight ⊆ rectangle p (last + 1) highHeight := by
      intro lowHeight highHeight hheight position hposition
      simp only [rectangle, Finset.mem_filter] at *
      exact ⟨hposition.1, le_trans hposition.2 hheight⟩
    have heq : ({first, middle, last} : Finset ℕ) = {otherFirst, otherMiddle, last} := by
      rcases le_total (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0))
          (max (max (p.getD otherFirst 0) (p.getD otherMiddle 0)) (p.getD last 0)) with
        hle | hle
      · apply Finset.eq_of_subset_of_card_le _ hcard.ge
        rw [← hrect, ← hotherRect]
        exact hsubset _ _ hle
      · apply Eq.symm
        apply Finset.eq_of_subset_of_card_le _ hcard.le
        rw [← hrect, ← hotherRect]
        exact hsubset _ _ hle
    exact hsorted first middle last otherFirst otherMiddle last
      hfirst hmiddle hotherFirst hotherMiddle heq
  have hmaximumUnique : ∀ (inc otherInc : Bool) (left right : ℕ × ℕ × ℕ),
      IsOccurrence inc p left → IsOccurrence otherInc p right →
      max (max (p.getD left.1 0) (p.getD left.2.1 0)) (p.getD left.2.2 0) =
        max (max (p.getD right.1 0) (p.getD right.2.1 0)) (p.getD right.2.2 0) →
      left = right := by
    intro inc otherInc left right hleft hright hmaximum
    have hleftEq := ((hcriterion inc left.1 left.2.1 left.2.2).mp hleft).2.2.2.2.2
    have hrightEq := ((hcriterion otherInc right.1 right.2.1 right.2.2).mp hright).2.2.2.2.2
    exact hlastUnique inc otherInc left right hleft hright (by omega)
  refine ⟨hcriterion, hmaximumUnique, hlastUnique, ?_⟩
  intro inc
  classical
  have hlength : p.length = n := by simpa using hp.length_eq
  have hvalues : ∀ position < p.length, p.getD position 0 ≤ n := by
    intro position hposition
    have hmem := hp.mem_iff.mp (List.getElem_mem hposition)
    rw [List.mem_range'_1] at hmem
    rw [List.getD_eq_getElem p 0 hposition]
    omega
  unfold occ
  apply Set.ncard_congr
    (fun triple _ => max (max (p.getD triple.1 0) (p.getD triple.2.1 0))
      (p.getD triple.2.2 0))
  · rintro ⟨first, middle, last⟩ hocc
    obtain ⟨hfirst, hmiddle, hlast, horder, hrect, hsum⟩ :=
      (hcriterion inc first middle last).mp hocc
    have hfirstbound := hvalues first (by omega)
    have hmiddlebound := hvalues middle (by omega)
    have hlastbound := hvalues last hlast
    have hwidth : last + 1 =
        n - max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) + 3 := by
      omega
    refine ⟨first, middle, last, hfirst, hmiddle, hlast, horder, rfl, ?_, hwidth⟩
    simpa only [← hwidth] using hrect
  · intro left right hleft hright heq
    exact hmaximumUnique inc inc left right hleft hright heq
  · rintro maximum ⟨first, middle, last, hfirst, hmiddle, hlast, horder,
      hmaximum, hrect, hwidth⟩
    have hfirstbound := hvalues first (by omega)
    have hmiddlebound := hvalues middle (by omega)
    have hlastbound := hvalues last hlast
    refine ⟨(first, middle, last), ?_, hmaximum⟩
    apply (hcriterion inc first middle last).mpr
    refine ⟨hfirst, hmiddle, hlast, horder, ?_, ?_⟩
    · simpa only [hmaximum, hwidth] using hrect
    · omega

def ferrersRegion (n : ℕ) : Set (ℕ × ℕ) :=
  {cell | ∃ maximum, 3 ≤ maximum ∧ maximum ≤ n ∧
    1 ≤ cell.1 ∧ cell.1 ≤ n - maximum + 3 ∧ 1 ≤ cell.2 ∧ cell.2 ≤ maximum}

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21
