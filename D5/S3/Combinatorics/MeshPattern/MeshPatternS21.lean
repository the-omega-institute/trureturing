/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21
   mirror-E: none(waiver:seven-state-joint-bijection)
   anchors: []
   utility: none
   digest: The seven-state permutation involution exchanges the two mesh occurrence counts. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21

open MeshPatternS21Defs

theorem result : MeshPatternS21Defs.claim := by
  classical
  have rectangle_criterion (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
      (∀ (inc : Bool) (first middle last : ℕ), IsOccurrence inc p (first, middle, last) ↔
        first < middle ∧ middle < last ∧ last < p.length ∧
          (if inc then p.getD first 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD last 0
            else p.getD last 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD first 0) ∧
          rectangle p (last + 1) (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)) =
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
      (∀ inc : Bool, occ inc p = {maximum | ∃ first middle last,
          first < middle ∧ middle < last ∧ last < p.length ∧
          (if inc then p.getD first 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD last 0
            else p.getD last 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD first 0) ∧
          max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) = maximum ∧
          rectangle p (n - maximum + 3) maximum = {first, middle, last} ∧
          last + 1 = n - maximum + 3}.ncard) := by
    have hshading (p : List ℕ) (hp : p.Nodup) (first middle last : ℕ)
        (hfirst : first < middle) (hmiddle : middle < last) (hlast : last < p.length) :
        (∀ position < p.length, position ≠ first → position ≠ middle → position ≠ last →
          ¬ Shaded (column first middle last position)
            (row (p.getD first 0) (p.getD middle 0) (p.getD last 0) (p.getD position 0))) ↔
        (∀ position < p.length, position ≠ first → position ≠ middle → position ≠ last →
          (position < last → max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) <
              p.getD position 0) ∧
          (last < position → p.getD position 0 <
              max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0))) := by
      have hindex : ∀ left right, left < p.length → right < p.length →
          p.getD left 0 = p.getD right 0 → left = right := by
        intro left right hleft hright heq
        rw [List.getD_eq_getElem p 0 hleft, List.getD_eq_getElem p 0 hright] at heq
        exact hp.getElem_inj_iff.mp heq
      have hlocal : ∀ position < p.length, position ≠ first → position ≠ middle → position ≠ last →
          ((¬ Shaded (column first middle last position)
            (row (p.getD first 0) (p.getD middle 0) (p.getD last 0) (p.getD position 0))) ↔
          ((position < last → max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) <
              p.getD position 0) ∧
          (last < position → p.getD position 0 <
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
    have hcriterion : ∀ (inc : Bool) (first middle last : ℕ),
        IsOccurrence inc p (first, middle, last) ↔
        first < middle ∧ middle < last ∧ last < p.length ∧
          (if inc then p.getD first 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD last 0
            else p.getD last 0 < p.getD middle 0 ∧ p.getD middle 0 < p.getD first 0) ∧
          rectangle p (last + 1) (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)) =
              {first, middle, last} ∧
          last + 1 + max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) = n + 3 := by
      intro inc first middle last
      classical
      have hlength : p.length = n := by simpa using hp.length_eq
      have hnodup : p.Nodup := hp.nodup_iff.mpr (List.nodup_range')
      have hindex : ∀ left right, left < n → right < n →
          p.getD left 0 = p.getD right 0 → left = right := by
        intro left right hleft hright heq
        rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 (by omega)] at heq
        exact hnodup.getElem_inj_iff.mp heq
      have hvalues : ∀ position < n, 1 ≤ p.getD position 0 ∧ p.getD position 0 ≤ n := by
        intro position hposition
        have hmem := hp.mem_iff.mp (List.getElem_mem (l := p) (n := position) (by omega))
        rw [List.mem_range'_1] at hmem
        rw [List.getD_eq_getElem p 0 (by omega)]
        omega
      suffices ∀ (hfirst : first < middle) (hmiddle : middle < last) (hlast : last < p.length),
          (∀ position < p.length, position ≠ first → position ≠ middle → position ≠ last →
            ¬ Shaded (column first middle last position)
              (row (p.getD first 0) (p.getD middle 0) (p.getD last 0) (p.getD position 0))) ↔
          (rectangle p (last + 1) (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)) =
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
          have hrightbound : right < n := (Finset.mem_filter.mp hright).1 |> Finset.mem_range.mp
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
      rw [hshading p hnodup first middle last hfirst hmiddle hlast]
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
          have hbound : position < n ∧ ¬position < last + 1 := by simpa [suffix] using hposition
          have hsmall := (hsep position (by omega) (by omega) (by omega) (by omega)).2 (by omega)
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
      obtain ⟨hfirst, hmiddle, _, _, hrect, _⟩ := (hcriterion inc first middle last).mp hleft
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
    apply Set.ncard_congr (fun triple _ => max (max (p.getD triple.1 0) (p.getD triple.2.1 0))
        (p.getD triple.2.2 0))
    · rintro ⟨first, middle, last⟩ hocc
      obtain ⟨hfirst, hmiddle, hlast, horder, hrect, hsum⟩ :=
        (hcriterion inc first middle last).mp hocc
      have hfirstbound := hvalues first (by omega)
      have hmiddlebound := hvalues middle (by omega)
      have hlastbound := hvalues last hlast
      have hwidth : last + 1 =
          n - max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0) + 3 := by omega
      refine ⟨first, middle, last, hfirst, hmiddle, hlast, horder, rfl, ?_, hwidth⟩
      simpa only [← hwidth] using hrect
    · intro left right hleft hright heq
      exact hmaximumUnique inc inc left right hleft hright heq
    · rintro maximum ⟨first, middle, last, hfirst, hmiddle, hlast, horder, hmaximum, hrect, hwidth⟩
      have hfirstbound := hvalues first (by omega)
      have hmiddlebound := hvalues middle (by omega)
      have hlastbound := hvalues last hlast
      refine ⟨(first, middle, last), ?_, hmaximum⟩
      apply (hcriterion inc first middle last).mpr
      refine ⟨hfirst, hmiddle, hlast, horder, ?_, ?_⟩
      · simpa only [hmaximum, hwidth] using hrect
      · omega
  have seven_switch_involution (n : ℕ) : ∃ switch : {p : List ℕ // p.Perm (List.range' 1 n)} →
          {p : List ℕ // p.Perm (List.range' 1 n)},
        Function.Involutive switch ∧
        (∀ p, active n (switch p).val = active n p.val ∧
          activeRegion n (switch p).val = activeRegion n p.val) ∧
        (∀ p x y, 1 ≤ x → x ≤ n → (x, y) ∉ activeRegion n p.val →
          ((switch p).val.getD (x - 1) 0 = y ↔ p.val.getD (x - 1) 0 = y)) ∧
        (∀ p maximum, 3 ≤ maximum → maximum ≤ n →
          (rectangle (switch p).val (n - maximum + 3) maximum).card =
            (rectangle p.val (n - maximum + 3) maximum).card ∧
          ((∃ position ∈ rectangle (switch p).val (n - maximum + 3) maximum,
            (switch p).val.getD position 0 = maximum) ↔
            (∃ position ∈ rectangle p.val (n - maximum + 3) maximum,
              p.val.getD position 0 = maximum)) ∧
          (n - maximum + 2 ∈ rectangle (switch p).val (n - maximum + 3) maximum ↔
            n - maximum + 2 ∈ rectangle p.val (n - maximum + 3) maximum)) ∧
        (∀ p,
          let directions := sevenOutline (activeRegion n p.val) n 0 n
          sevenBoundary (fun x y => (sevenDiagram (switch p).val x y).getD .empty) 0 directions =
              (sevenBoundary (fun x y => (sevenDiagram p.val x y).getD .empty)
                0 directions).map (fun step => (step.1, step.2.transpose))) := by
    classical
    let shape := fun p : {p : List ℕ // p.Perm (List.range' 1 n)} =>
      sevenOutline (activeRegion n p.val) n 0 n
    let labels := fun (p : {p : List ℕ // p.Perm (List.range' 1 n)}) x y =>
      (sevenDiagram p.val x y).getD SevenLabel.empty
    let boundary := fun p => sevenBoundary (labels p) 0 (shape p)
    let trace := fun (p : {p : List ℕ // p.Perm (List.range' 1 n)}) directions =>
      (sevenCells 0 directions).map (fun cell =>
        (cell.1, cell.2, decide (p.val.getD (cell.1 - 1) 0 = cell.2)))
    let conjugate := fun path : List (Bool × SevenLabel) =>
      path.map (fun step => (step.1, step.2.transpose))
    have hexists := fun p : {p : List ℕ // p.Perm (List.range' 1 n)} =>
      (seven_active_switch n p.val p.property).2
    dsimp only at hexists
    choose candidate axes hperm hcomputed hempty houtside hstats hactive hregion using hexists
    let switch := fun p => (⟨candidate p, hperm p⟩ : {p : List ℕ // p.Perm (List.range' 1 n)})
    have hshape : ∀ p, shape (switch p) = shape p := by
      intro p
      dsimp only [shape, switch]
      rw [hregion p]
    have hboundaryShape : ∀ directions column p,
        (sevenBoundary (labels p) column directions).map Prod.fst = directions := by
      intro directions
      induction directions with
      | nil => intro column p; rfl
      | cons direction tail ih =>
        intro column p
        cases direction <;> simp [sevenBoundary, ih]
    have htranspose : ∀ label : SevenLabel, label.transpose.transpose = label := by
      intro label
      cases label <;> rfl
    have hdouble : ∀ path, conjugate (conjugate path) = path := by
      intro path
      simp [conjugate, List.map_map, Function.comp_def, htranspose]
    have hedge : ∀ smaller larger : SevenLabel,
        sevenEdge smaller.transpose larger.transpose = sevenEdge smaller larger := by
      intro smaller larger; cases smaller <;> cases larger <;> rfl
    have hconjugatePath : ∀ path start, sevenPath start path →
        sevenPath start.transpose (conjugate path) := by
      intro path
      induction path with
      | nil => intro start hpath; trivial
      | cons step tail ih =>
        obtain ⟨direction, next⟩ := step
        intro start hpath; cases direction <;>
          simpa [conjugate, sevenPath, hedge] using And.intro hpath.1 (ih next hpath.2)
    have haxesEqual : ∀ (first second firstAxes secondAxes : List (Bool × SevenLabel))
        (firstTrace secondTrace : List (ℕ × ℕ × Bool)),
        sevenPath .empty first → sevenPath .empty second →
        first.map Prod.fst = second.map Prod.fst →
        sevenPeel .empty 0 first = some (firstAxes, firstTrace) →
        sevenPeel .empty 0 second = some (secondAxes, secondTrace) →
        (∀ step ∈ firstAxes, step.2 = .empty) →
        (∀ step ∈ secondAxes, step.2 = .empty) → firstAxes = secondAxes := by
      intro first second firstAxes secondAxes firstTrace secondTrace hfirst hsecond
        hshape hfirstPeel hsecondPeel hfirstEmpty hsecondEmpty
      obtain ⟨actualFirstAxes, actualFirstTrace, hactualFirst, _, hfirstSorted, hfirstPerm,
          _, _⟩ := seven_boundary_peeling .empty 0 first hfirst
      obtain ⟨actualSecondAxes, actualSecondTrace, hactualSecond, _, hsecondSorted,
          hsecondPerm, _, _⟩ := seven_boundary_peeling .empty 0 second hsecond
      have hfirstEq := Option.some.inj (hfirstPeel.symm.trans hactualFirst)
      have hsecondEq := Option.some.inj (hsecondPeel.symm.trans hactualSecond)
      have hfirstAxes : firstAxes = actualFirstAxes := (Prod.mk.inj hfirstEq).1
      have hsecondAxes : secondAxes = actualSecondAxes := (Prod.mk.inj hsecondEq).1
      rw [← hfirstAxes] at hfirstSorted hfirstPerm
      rw [← hsecondAxes] at hsecondSorted hsecondPerm
      have haxesShape : firstAxes.map Prod.fst = secondAxes.map Prod.fst := by
        apply List.Perm.eq_of_pairwise (le := fun first second : Bool =>
          first = false ∨ second = true)
        · intro first second hfirst hsecond hforward hbackward
          cases first <;> cases second <;> simp at hforward hbackward ⊢
        · simpa only [List.pairwise_map] using hfirstSorted
        · simpa only [List.pairwise_map] using hsecondSorted
        · rw [hshape] at hfirstPerm
          exact hfirstPerm.trans hsecondPerm.symm
      have hnormalize : ∀ path : List (Bool × SevenLabel), (∀ step ∈ path, step.2 = .empty) →
          path = path.map (fun step => (step.1, SevenLabel.empty)) := by
        intro path hall
        conv_lhs => rw [← List.map_id path]
        apply List.map_congr_left
        intro step hstep; exact Prod.ext rfl (hall step hstep)
      rw [hnormalize firstAxes hfirstEmpty, hnormalize secondAxes hsecondEmpty]
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun direction => (direction, SevenLabel.empty))) haxesShape
    have hcompatibility : ∀ p, boundary (switch p) = conjugate (boundary p) := by
      intro p
      obtain ⟨_, _, _, hpPath, hpAxes, hpPeel, hpEmpty⟩ :=
        (seven_active_switch n p.val p.property).1
      obtain ⟨_, _, _, hqPath, hqAxes, hqPeel, hqEmpty⟩ :=
        (seven_active_switch n (switch p).val (switch p).property).1
      have hqComputed : sevenPeel .empty 0 (boundary (switch p)) =
          some (hqAxes, trace (switch p) (shape p)) := by
        have hread : sevenPeel .empty 0 (boundary (switch p)) =
            some (hqAxes, trace (switch p) (shape (switch p))) := hqPeel
        rw [hshape p] at hread
        exact hread
      have hpComputed : sevenPeel .empty 0 (conjugate (boundary p)) =
          some (axes p, trace (switch p) (shape p)) := hcomputed p
      have hpTransPath : sevenPath .empty (conjugate (boundary p)) := by
        simpa only [SevenLabel.transpose] using hconjugatePath (boundary p) .empty hpPath
      have hsameShape : (boundary (switch p)).map Prod.fst =
          (conjugate (boundary p)).map Prod.fst := by
        simp only [boundary, conjugate, List.map_map, Function.comp_def]
        rw [hboundaryShape, hboundaryShape, hshape p]
      have hsameAxes := haxesEqual (boundary (switch p)) (conjugate (boundary p))
        hqAxes (axes p) (trace (switch p) (shape p)) (trace (switch p) (shape p))
        hqPath hpTransPath hsameShape hqComputed hpComputed hqEmpty (hempty p)
      rw [hsameAxes] at hqComputed
      exact seven_peeling_unique .empty 0 (boundary (switch p)) (conjugate (boundary p))
        (axes p) (trace (switch p) (shape p)) hsameShape hqPath hpTransPath
        hqComputed hpComputed
    have hinvolutive : Function.Involutive switch := by
      intro p
      have htwiceBoundary : conjugate (boundary (switch p)) = boundary p := by
        rw [hcompatibility p, hdouble]
      obtain ⟨_, _, hcoverage, _, originalAxes, horiginal, _⟩ :=
        (seven_active_switch n p.val p.property).1
      have htwiceComputed : sevenPeel .empty 0 (boundary p) =
          some (axes (switch p), trace (switch (switch p)) (shape p)) := by
        have hread : sevenPeel .empty 0 (conjugate (boundary (switch p))) =
            some (axes (switch p), trace (switch (switch p)) (shape (switch p))) :=
          hcomputed (switch p)
        simpa only [htwiceBoundary, hshape p] using hread
      have htraceEqual : trace (switch (switch p)) (shape p) = trace p (shape p) :=
        congrArg Prod.snd (Option.some.inj (htwiceComputed.symm.trans horiginal))
      apply Subtype.ext
      have hlength : (switch (switch p)).val.length = p.val.length :=
        (switch (switch p)).property.length_eq.trans p.property.length_eq.symm
      apply List.ext_getElem hlength
      intro position hleft hright
      have hbound : position < n := by
        have := p.property.length_eq
        simp only [List.length_range'] at this
        omega
      have hvalue : (switch (switch p)).val.getD position 0 = p.val.getD position 0 := by
        by_cases hinside : (position + 1, p.val.getD position 0) ∈ activeRegion n p.val
        · have hcoordinate : (position + 1, p.val.getD position 0) ∈ sevenCells 0 (shape p) :=
            (hcoverage _).mpr hinside
          have hmem : (position + 1, p.val.getD position 0, true) ∈ trace p (shape p) := by
            apply List.mem_map.mpr
            exact ⟨(position + 1, p.val.getD position 0), hcoordinate, by simp⟩
          rw [← htraceEqual] at hmem
          obtain ⟨cell, _, heq⟩ := List.mem_map.mp hmem
          have hx := congrArg Prod.fst heq
          have hy := congrArg (fun entry => entry.2.1) heq
          have hbit := congrArg (fun entry => entry.2.2) heq
          change cell.1 = position + 1 at hx
          change cell.2 = p.val.getD position 0 at hy
          have hget := of_decide_eq_true hbit
          simpa only [hx, hy, Nat.add_sub_cancel] using hget
        · have hpOutside := houtside p (position + 1) (p.val.getD position 0)
            (by omega) (by omega) hinside
          have hqOutside := houtside (switch p) (position + 1) (p.val.getD position 0)
            (by omega) (by omega) (by
              change (position + 1, p.val.getD position 0) ∉ activeRegion n (candidate p)
              rw [hregion p]
              exact hinside)
          simpa only [Nat.add_sub_cancel] using hqOutside.mpr (hpOutside.mpr (by simp))
      simpa only [List.getD_eq_getElem (switch (switch p)).val 0 hleft,
        List.getD_eq_getElem p.val 0 hright] using hvalue
    refine ⟨switch, hinvolutive, ?_, houtside, hstats, ?_⟩
    · intro p
      exact ⟨hactive p, hregion p⟩
    · intro p
      simpa only [boundary, labels, hshape p] using hcompatibility p
  intro n k l
  obtain ⟨switch, hinvolution, hregion, houtside, hstatistics, hboundary⟩ :=
    seven_switch_involution n
  let events := fun (p : {p : List ℕ // p.Perm (List.range' 1 n)}) (inc : Bool) =>
    {maximum | ∃ first middle last,
      first < middle ∧ middle < last ∧ last < p.val.length ∧
      (if inc then p.val.getD first 0 < p.val.getD middle 0 ∧
        p.val.getD middle 0 < p.val.getD last 0
        else p.val.getD last 0 < p.val.getD middle 0 ∧ p.val.getD middle 0 < p.val.getD first 0) ∧
      max (max (p.val.getD first 0) (p.val.getD middle 0)) (p.val.getD last 0) = maximum ∧
      rectangle p.val (n - maximum + 3) maximum = {first, middle, last} ∧
      last + 1 = n - maximum + 3}
  have hordered : ∀ cells : Finset ℕ, cells.card = 3 →
      ∃ first middle last, first < middle ∧ middle < last ∧ cells = {first, middle, last} := by
    intro cells hcard
    obtain ⟨first, middle, last, hfirstMiddle, hfirstLast, hmiddleLast, hset⟩ :=
      Finset.card_eq_three.mp hcard
    rcases lt_or_gt_of_ne hfirstMiddle with hfirstMiddle | hmiddleFirst
    · rcases lt_or_gt_of_ne hmiddleLast with hmiddleLast | hlastMiddle
      · exact ⟨first, middle, last, hfirstMiddle, hmiddleLast, hset⟩
      · rcases lt_or_gt_of_ne hfirstLast with hfirstLast | hlastFirst
        · exact ⟨first, last, middle, hfirstLast, hlastMiddle, by
            rw [hset]; ext position; simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto⟩
        · exact ⟨last, first, middle, hlastFirst, hfirstMiddle, by
            rw [hset]; ext position; simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto⟩
    · rcases lt_or_gt_of_ne hfirstLast with hfirstLast | hlastFirst
      · exact ⟨middle, first, last, hmiddleFirst, hfirstLast, by
          rw [hset]; ext position; simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto⟩
      · rcases lt_or_gt_of_ne hmiddleLast with hmiddleLast | hlastMiddle
        · exact ⟨middle, last, first, hmiddleLast, hlastFirst, by
            rw [hset]; ext position; simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto⟩
        · exact ⟨last, middle, first, hlastMiddle, hmiddleFirst, by
            rw [hset]; ext position; simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto⟩
  have hcharacter : ∀ (p : {p : List ℕ // p.Perm (List.range' 1 n)}) inc maximum,
      maximum ∈ events p inc ↔ maximum ∈ active n p.val ∧
        (∃ position ∈ rectangle p.val (n - maximum + 3) maximum, p.val.getD position 0 = maximum) ∧
        n - maximum + 2 ∈ rectangle p.val (n - maximum + 3) maximum ∧
        (if inc then StrictMonoOn (fun position => p.val.getD position 0)
          (rectangle p.val (n - maximum + 3) maximum)
          else StrictAntiOn (fun position => p.val.getD position 0)
            (rectangle p.val (n - maximum + 3) maximum)) := by
    intro p inc maximum
    have hlength : p.val.length = n := by simpa using p.property.length_eq
    have hvalues : ∀ position < n, 1 ≤ p.val.getD position 0 ∧ p.val.getD position 0 ≤ n := by
      intro position hposition
      have hmem := p.property.mem_iff.mp (List.getElem_mem (show position < p.val.length by omega))
      rw [List.mem_range'_1] at hmem
      rw [List.getD_eq_getElem p.val 0 (by omega)]
      exact ⟨hmem.1, by omega⟩
    constructor
    · rintro ⟨first, middle, last, hfirst, hmiddle, hlast, horder, hmaximum, hset, hwidth⟩
      have hfirstValues := hvalues first (by omega)
      have hmiddleValues := hvalues middle (by omega)
      have hlastValues := hvalues last (by omega)
      have hmaximumBounds : 3 ≤ maximum ∧ maximum ≤ n := by
        cases inc <;> simp only [Bool.false_eq_true, ↓reduceIte] at horder <;> omega
      have hcard : (rectangle p.val (n - maximum + 3) maximum).card = 3 := by
        rw [hset]
        simp [ne_of_lt hfirst, ne_of_lt hmiddle, ne_of_lt (lt_trans hfirst hmiddle)]
      have hactive : maximum ∈ active n p.val := by
        simp only [active, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hmaximumBounds.1, hcard⟩
      have hrow : ∃ position ∈ rectangle p.val (n - maximum + 3) maximum,
          p.val.getD position 0 = maximum := by
        by_cases hfirstEqual : p.val.getD first 0 = maximum
        · exact ⟨first, by rw [hset]; simp, hfirstEqual⟩
        by_cases hmiddleEqual : p.val.getD middle 0 = maximum
        · exact ⟨middle, by rw [hset]; simp, hmiddleEqual⟩
        exact ⟨last, by rw [hset]; simp, by omega⟩
      have hcolumn : n - maximum + 2 ∈ rectangle p.val (n - maximum + 3) maximum := by
        have heq : n - maximum + 2 = last := by omega
        rw [heq, hset]
        simp
      refine ⟨hactive, hrow, hcolumn, ?_⟩
      cases inc <;> simp only [Bool.false_eq_true, ↓reduceIte] at horder ⊢
      all_goals
        intro left hleft right hright hlt; rw [hset] at hleft hright
        have hleftChoice : left = first ∨ left = middle ∨ left = last := by simpa using hleft
        have hrightChoice : right = first ∨ right = middle ∨ right = last := by simpa using hright
        rcases hleftChoice with rfl | rfl | rfl <;>
          rcases hrightChoice with rfl | rfl | rfl
        all_goals dsimp only; omega
    · rintro ⟨hactive, hrow, hcolumn, horder⟩
      have hactiveData : 3 ≤ maximum ∧ maximum ≤ n ∧
          (rectangle p.val (n - maximum + 3) maximum).card = 3 := by
        simp only [active, Finset.mem_filter, Finset.mem_range] at hactive
        exact ⟨hactive.2.1, by omega, hactive.2.2⟩
      obtain ⟨first, middle, last, hfirst, hmiddle, hset⟩ :=
        hordered (rectangle p.val (n - maximum + 3) maximum) hactiveData.2.2
      have hfirstMem : first ∈ rectangle p.val (n - maximum + 3) maximum := by rw [hset]; simp
      have hmiddleMem : middle ∈ rectangle p.val (n - maximum + 3) maximum := by rw [hset]; simp
      have hlastMem : last ∈ rectangle p.val (n - maximum + 3) maximum := by rw [hset]; simp
      have hlastBound : last < p.val.length := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hlastMem).1
        omega
      have hwidth : last + 1 = n - maximum + 3 := by
        have hlastPosition := Finset.mem_range.mp (Finset.mem_filter.mp hlastMem).1
        rw [hset] at hcolumn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcolumn
        omega
      have hmaximum : max (max (p.val.getD first 0) (p.val.getD middle 0))
          (p.val.getD last 0) = maximum := by
        have hfirstValue := (Finset.mem_filter.mp hfirstMem).2
        have hmiddleValue := (Finset.mem_filter.mp hmiddleMem).2
        have hlastValue := (Finset.mem_filter.mp hlastMem).2
        obtain ⟨position, hposition, hvalue⟩ := hrow
        rw [hset] at hposition
        simp only [Finset.mem_insert, Finset.mem_singleton] at hposition
        rcases hposition with rfl | rfl | rfl <;> omega
      refine ⟨first, middle, last, hfirst, hmiddle, hlastBound, ?_, hmaximum, hset, hwidth⟩
      cases inc <;> simp only [Bool.false_eq_true, ↓reduceIte] at horder ⊢
      · exact ⟨horder hmiddleMem hlastMem hmiddle, horder hfirstMem hmiddleMem hfirst⟩
      · exact ⟨horder hfirstMem hmiddleMem hfirst, horder hmiddleMem hlastMem hmiddle⟩
  have htransposeBoundary : ∀ directions column (labels : ℕ → ℕ → SevenLabel),
      (sevenBoundary labels column directions).map (fun step => (step.1, step.2.transpose)) =
        sevenBoundary (fun x y => (labels x y).transpose) column directions := by
    intro directions
    induction directions with
    | nil => intro column labels; rfl
    | cons direction tail ih =>
      intro column labels
      cases direction <;> simp [sevenBoundary, ih]
  have hdrop : ∀ beforePath afterPath column (labels : ℕ → ℕ → SevenLabel),
      (sevenBoundary labels column (beforePath ++ afterPath)).drop beforePath.length =
        sevenBoundary labels (column + beforePath.count true) afterPath := by
    intro beforePath
    induction beforePath with
    | nil => intro afterPath column labels; simp
    | cons direction tail ih =>
      intro afterPath column labels
      cases direction with
      | false => simpa [sevenBoundary] using ih afterPath column labels
      | true =>
        simpa [sevenBoundary, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih afterPath (column + 1) labels
  have horders : ∀ (p : {p : List ℕ // p.Perm (List.range' 1 n)}) maximum,
      maximum ∈ active n p.val →
      (StrictMonoOn (fun position => p.val.getD position 0)
          (rectangle p.val (n - maximum + 3) maximum) ↔
        StrictAntiOn (fun position => (switch p).val.getD position 0)
          (rectangle (switch p).val (n - maximum + 3) maximum)) ∧
      (StrictAntiOn (fun position => p.val.getD position 0)
          (rectangle p.val (n - maximum + 3) maximum) ↔
        StrictMonoOn (fun position => (switch p).val.getD position 0)
          (rectangle (switch p).val (n - maximum + 3) maximum)) := by
    intro p maximum hmaximum
    have hdata : 3 ≤ maximum ∧ maximum ≤ n ∧
        (rectangle p.val (n - maximum + 3) maximum).card = 3 := by
      simp only [active, Finset.mem_filter, Finset.mem_range] at hmaximum
      exact ⟨hmaximum.2.1, by omega, hmaximum.2.2⟩
    have hqCard : (rectangle (switch p).val (n - maximum + 3) maximum).card = 3 :=
      ((hstatistics p maximum hdata.1 hdata.2.1).1).trans hdata.2.2
    obtain ⟨left, hleft, hleftSize, _, _⟩ := seven_state_construction n p.val p.property
      (n - maximum + 3) (by omega) maximum hdata.2.1 (by omega)
    obtain ⟨right, hright, hrightSize, _, _⟩ := seven_state_construction n
      (switch p).val (switch p).property (n - maximum + 3) (by omega)
      maximum hdata.2.1 (by omega)
    rw [hdata.2.2] at hleftSize
    rw [hqCard] at hrightSize
    obtain ⟨beforePath, afterPath, hshape, hwidth, hheight⟩ :=
      seven_corner_boundary n p.val maximum hmaximum
    have hread := hboundary p
    dsimp only at hread
    rw [htransposeBoundary, hshape] at hread
    have hdropped := congrArg (List.drop beforePath.length) hread
    rw [hdrop, hdrop] at hdropped
    have hlabels : right = left.transpose := by
      have hhead := congrArg List.head? hdropped
      simp only [sevenBoundary, List.head?_cons, Nat.zero_add, hwidth, hheight,
        hleft, hright, Option.getD_some, Option.some.injEq, Prod.mk.injEq, true_and] at hhead
      exact hhead
    have hleftOrders := seven_order_interpretation n p.val p.property
      (n - maximum + 3) (by omega) maximum hdata.2.1 left hleft (by omega)
    have hrightOrders := seven_order_interpretation n (switch p).val (switch p).property
      (n - maximum + 3) (by omega) maximum hdata.2.1 right hright (by omega)
    rw [hlabels] at hrightOrders hrightSize
    constructor
    · rw [hleftOrders.1, hrightOrders.2]
      cases left <;> simp [SevenLabel.size] at hleftSize <;> simp [SevenLabel.transpose]
    · rw [hleftOrders.2, hrightOrders.1]
      cases left <;> simp [SevenLabel.size] at hleftSize <;> simp [SevenLabel.transpose]
  have hevents : ∀ p inc, events p inc = events (switch p) (!inc) := by
    intro p inc
    ext maximum
    rw [hcharacter, hcharacter, (hregion p).1]
    by_cases hmaximum : maximum ∈ active n p.val
    · have hdata : 3 ≤ maximum ∧ maximum ≤ n := by
        simp only [active, Finset.mem_filter, Finset.mem_range] at hmaximum
        exact ⟨hmaximum.2.1, by omega⟩
      have hstats := hstatistics p maximum hdata.1 hdata.2
      rw [hstats.2.1, hstats.2.2]
      have horder := horders p maximum hmaximum
      cases inc with
      | false =>
        simpa only [Bool.not_false, Bool.false_eq_true, ↓reduceIte] using
          (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl horder.2)))
      | true =>
        simpa only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] using
          (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl horder.1)))
    · simp only [hmaximum, false_and]
  have hcounts : ∀ p inc, MeshPatternS21Defs.occ inc p.val =
      MeshPatternS21Defs.occ (!inc) (switch p).val := by
    intro p inc
    rw [(rectangle_criterion n p.val p.property).2.2.2 inc,
      (rectangle_criterion n (switch p).val (switch p).property).2.2.2 (!inc)]
    exact congrArg Set.ncard (hevents p inc)
  let forward := fun p : {p : List ℕ // p ∈ MeshPatternS21Defs.joint n k l} =>
    (⟨(switch ⟨p.val, p.property.1⟩).val, by
      have hp := p.property
      have htrue := hcounts ⟨p.val, hp.1⟩ false
      have hfalse := hcounts ⟨p.val, hp.1⟩ true
      exact ⟨(switch ⟨p.val, hp.1⟩).property, htrue.symm.trans hp.2.2, hfalse.symm.trans hp.2.1⟩⟩ :
      {p : List ℕ // p ∈ MeshPatternS21Defs.joint n l k})
  let backward := fun p : {p : List ℕ // p ∈ MeshPatternS21Defs.joint n l k} =>
    (⟨(switch ⟨p.val, p.property.1⟩).val, by
      have hp := p.property
      have htrue := hcounts ⟨p.val, hp.1⟩ false
      have hfalse := hcounts ⟨p.val, hp.1⟩ true
      exact ⟨(switch ⟨p.val, hp.1⟩).property, htrue.symm.trans hp.2.2, hfalse.symm.trans hp.2.1⟩⟩ :
      {p : List ℕ // p ∈ MeshPatternS21Defs.joint n k l})
  apply Set.ncard_congr'
  refine ⟨forward, backward, ?_, ?_⟩
  · intro p
    apply Subtype.ext
    change (switch (switch ⟨p.val, p.property.1⟩)).val = p.val
    exact congrArg Subtype.val (hinvolution ⟨p.val, p.property.1⟩)
  · intro p
    apply Subtype.ext
    change (switch (switch ⟨p.val, p.property.1⟩)).val = p.val
    exact congrArg Subtype.val (hinvolution ⟨p.val, p.property.1⟩)

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21
