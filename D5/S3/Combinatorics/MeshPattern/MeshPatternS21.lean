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

theorem result : MeshPatternS21Defs.claim := by
  classical
  intro n k l
  obtain ⟨switch, hinvolution, hregion, houtside, hstatistics, hboundary⟩ :=
    seven_switch_involution n
  let events := fun (p : {p : List ℕ // p.Perm (List.range' 1 n)}) (inc : Bool) =>
    {maximum | ∃ first middle last,
      first < middle ∧ middle < last ∧ last < p.val.length ∧
      (if inc then p.val.getD first 0 < p.val.getD middle 0 ∧
        p.val.getD middle 0 < p.val.getD last 0
        else p.val.getD last 0 < p.val.getD middle 0 ∧
          p.val.getD middle 0 < p.val.getD first 0) ∧
      max (max (p.val.getD first 0) (p.val.getD middle 0)) (p.val.getD last 0) = maximum ∧
      rectangle p.val (n - maximum + 3) maximum = {first, middle, last} ∧
      last + 1 = n - maximum + 3}
  have hordered : ∀ cells : Finset ℕ, cells.card = 3 →
      ∃ first middle last, first < middle ∧ middle < last ∧
        cells = {first, middle, last} := by
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
      maximum ∈ events p inc ↔
        maximum ∈ active n p.val ∧
        (∃ position ∈ rectangle p.val (n - maximum + 3) maximum,
          p.val.getD position 0 = maximum) ∧
        n - maximum + 2 ∈ rectangle p.val (n - maximum + 3) maximum ∧
        (if inc then StrictMonoOn (fun position => p.val.getD position 0)
          (rectangle p.val (n - maximum + 3) maximum)
          else StrictAntiOn (fun position => p.val.getD position 0)
            (rectangle p.val (n - maximum + 3) maximum)) := by
    intro p inc maximum
    have hlength : p.val.length = n := by simpa using p.property.length_eq
    have hvalues : ∀ position < n,
        1 ≤ p.val.getD position 0 ∧ p.val.getD position 0 ≤ n := by
      intro position hposition
      have hmem := p.property.mem_iff.mp
        (List.getElem_mem (show position < p.val.length by omega))
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
        intro left hleft right hright hlt
        rw [hset] at hleft hright
        have hleftChoice : left = first ∨ left = middle ∨ left = last := by simpa using hleft
        have hrightChoice : right = first ∨ right = middle ∨ right = last := by
          simpa using hright
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
      have hfirstMem : first ∈ rectangle p.val (n - maximum + 3) maximum := by
        rw [hset]; simp
      have hmiddleMem : middle ∈ rectangle p.val (n - maximum + 3) maximum := by
        rw [hset]; simp
      have hlastMem : last ∈ rectangle p.val (n - maximum + 3) maximum := by
        rw [hset]; simp
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
      seven_corner_boundary n p.val p.property maximum hmaximum
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
      exact ⟨(switch ⟨p.val, hp.1⟩).property,
        htrue.symm.trans hp.2.2, hfalse.symm.trans hp.2.1⟩⟩ :
      {p : List ℕ // p ∈ MeshPatternS21Defs.joint n l k})
  let backward := fun p : {p : List ℕ // p ∈ MeshPatternS21Defs.joint n l k} =>
    (⟨(switch ⟨p.val, p.property.1⟩).val, by
      have hp := p.property
      have htrue := hcounts ⟨p.val, hp.1⟩ false
      have hfalse := hcounts ⟨p.val, hp.1⟩ true
      exact ⟨(switch ⟨p.val, hp.1⟩).property,
        htrue.symm.trans hp.2.2, hfalse.symm.trans hp.2.1⟩⟩ :
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
