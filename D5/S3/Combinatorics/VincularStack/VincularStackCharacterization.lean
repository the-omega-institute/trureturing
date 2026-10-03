/- GID: D5/S3/Combinatorics/VincularStack/VincularStackCharacterization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackCharacterization
   mirror-E: none(waiver:explicit-mesh-avoidance-characterization)
   anchors: []
   utility: none
   digest: The sorting class is exactly the words avoiding 1324 and the shaded 2413 pattern. -/

import D5.S3.Combinatorics.VincularStack.VincularStackPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackMesh

open VincularStackDefs VincularStackBasic VincularStackRun VincularStackMarkers
open VincularStackCuts VincularStackSites VincularStackPrefixes VincularStackPatterns
open scoped List

def ContainsMesh2413 (word : List ℕ) : Prop :=
  ∃ first second third fourth, first < second ∧ second < third ∧ third < fourth ∧
    fourth < word.length ∧ word.getD third 0 < word.getD first 0 ∧
    word.getD first 0 < word.getD fourth 0 ∧ word.getD fourth 0 < word.getD second 0 ∧
    (∀ position < second, word.getD first 0 ≤ word.getD position 0) ∧
    (∀ position, second < position → position < third →
      ¬ (word.getD first 0 < word.getD position 0 ∧
        word.getD position 0 < word.getD second 0))

theorem maximum_insertion_obstruction (front suffix : List ℕ) (maximum : ℕ)
    (hnodup : (front ++ suffix).Nodup)
    (hbound : ∀ value ∈ front ++ suffix, value < maximum)
    (hparent : ¬ Contains231 (SC (front ++ suffix)))
    (hbad : Contains231 (SC (front ++ maximum :: suffix))) :
    Contains1324 (front ++ maximum :: suffix) ∨
      ContainsMesh2413 (front ++ maximum :: suffix) := by
  classical
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have hperm : (SC (front ++ suffix)).Perm (front ++ suffix) := by
    simpa [SC] using (process_preserves (front ++ suffix) [] hnil).1
  have hmarker := (maximum_insertion front suffix maximum hbound).1
  have hgapbad : ¬ separatingCut (SC (front ++ suffix)) (outputGap front suffix) := by
    intro hgap
    have hsplit := List.take_append_drop (outputGap front suffix) (SC (front ++ suffix))
    have hgaple : outputGap front suffix ≤ (SC (front ++ suffix)).length := by
      rw [hperm.length_eq]
      by_cases hfront : front = []
      · simp [outputGap, hfront]
      · exact le_of_lt ((maximum_insertion front suffix maximum hbound).2 hfront)
    have hcut := (maximum_cut
      ((SC (front ++ suffix)).take (outputGap front suffix))
      ((SC (front ++ suffix)).drop (outputGap front suffix)) maximum
      (by rw [hsplit]; exact hperm.nodup_iff.mpr hnodup)
      (by rw [hsplit]; intro value hvalue; exact hbound value (hperm.mem_iff.mp hvalue))).mpr
      ⟨by rwa [hsplit], by
        simpa only [hsplit, List.length_take, Nat.min_eq_left hgaple] using hgap⟩
    exact hcut (by rwa [← hmarker])
  have hfront : front ≠ [] := fun hempty =>
    hgapbad ((separating_gap front suffix).mpr (Or.inl hempty))
  have hfrontRead (position : ℕ) (hposition : position < front.length) :
      (front ++ maximum :: suffix).getD position 0 = front.getD position 0 :=
    List.getD_append front (maximum :: suffix) 0 position hposition
  have hmaxRead : (front ++ maximum :: suffix).getD front.length 0 = maximum := by
    rw [List.getD_append_right front (maximum :: suffix) 0 front.length (by omega)]
    simp
  by_cases hrecords : ∀ earlier next, earlier < next → next + 1 < front.length →
      front.getD (next + 1) 0 < front.getD next 0 →
      front.getD (next + 1) 0 ≤ front.getD earlier 0
  · right
    cases suffix with
    | nil =>
      exact False.elim (hgapbad ((separating_gap front []).mpr
        (Or.inr ⟨hrecords, trivial⟩)))
    | cons entry rest =>
      have htemporary : ¬ ∃ lower ∈ (snapshot front []).2, lower < entry := by
        intro htemporary
        exact hgapbad ((separating_gap front (entry :: rest)).mpr
          (Or.inr ⟨hrecords, Or.inl htemporary⟩))
      have hrelation : ¬ ∀ left ∈ entry :: rest, ∀ right ∈ front, left < right := by
        intro hrelation
        exact hgapbad ((separating_gap front (entry :: rest)).mpr
          (Or.inr ⟨hrecords, Or.inr hrelation⟩))
      obtain ⟨minimum, hminOption⟩ := Option.isSome_iff_exists.mp
        (List.isSome_min?_of_ne_nil hfront)
      obtain ⟨hminMem, hminBound⟩ := List.min?_eq_some_iff.mp hminOption
      have hminimumState := (snapshot_minimum front [] minimum hnil
        (by simpa using hminMem) (by simpa using hminBound)).2.1
      have hentryLe : entry ≤ minimum := Nat.le_of_not_gt
        (fun hless => htemporary ⟨minimum, hminimumState, hless⟩)
      have hdistinct : ∀ left ∈ entry :: rest, ∀ right ∈ front, left ≠ right := by
        intro left hleft right hright heq
        exact (List.nodup_append.mp hnodup).2.2 right hright left hleft heq.symm
      have hentryLt : entry < minimum := by
        have := hdistinct entry List.mem_cons_self minimum hminMem
        omega
      push Not at hrelation
      obtain ⟨upper, hupperMem, lower, hlowerMem, hupperLe⟩ := hrelation
      have hminUpper : minimum < upper := by
        have := hminBound lower hlowerMem
        have := hdistinct upper hupperMem minimum hminMem
        omega
      have hupperMax : upper < maximum := hbound upper (List.mem_append_right _ hupperMem)
      obtain ⟨minIndex, hminIndex, hminRead⟩ := List.mem_iff_getElem.mp hminMem
      obtain ⟨upperIndex, hupperIndex, hupperRead⟩ := List.mem_iff_getElem.mp hupperMem
      have hupperPositive : 0 < upperIndex := by
        by_contra hnot
        have hzero : upperIndex = 0 := by omega
        simp only [hzero, List.getElem_cons_zero] at hupperRead
        omega
      have hminD : front.getD minIndex 0 = minimum := by
        rw [List.getD_eq_getElem front 0 hminIndex, hminRead]
      have hupperD : (front ++ maximum :: entry :: rest).getD
          (front.length + 1 + upperIndex) 0 = upper := by
        rw [List.getD_append_right front (maximum :: entry :: rest) 0
          (front.length + 1 + upperIndex) (by omega)]
        have hoffset : front.length + 1 + upperIndex - front.length = upperIndex + 1 := by
          omega
        rw [hoffset, List.getD_cons_succ,
          List.getD_eq_getElem (entry :: rest) 0 hupperIndex, hupperRead]
      have hentryD : (front ++ maximum :: entry :: rest).getD (front.length + 1) 0 =
          entry := by
        rw [List.getD_append_right front (maximum :: entry :: rest) 0
          (front.length + 1) (by omega)]
        simp
      refine ⟨minIndex, front.length, front.length + 1,
        front.length + 1 + upperIndex, hminIndex, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons] at hupperIndex ⊢
        omega
      · rw [hentryD, hfrontRead minIndex hminIndex, hminD]
        exact hentryLt
      · rw [hfrontRead minIndex hminIndex, hminD, hupperD]
        exact hminUpper
      · rw [hupperD, hmaxRead]
        exact hupperMax
      · intro position hposition
        rw [hfrontRead minIndex hminIndex, hminD, hfrontRead position hposition]
        rw [List.getD_eq_getElem front 0 hposition]
        exact hminBound _ (List.getElem_mem hposition)
      · intro position hleft hright
        omega
  · left
    push Not at hrecords
    obtain ⟨earlier, next, hearlier, hnext, hdescent, hnotminimum⟩ := hrecords
    have hnextMax := hbound (front.getD next 0) (List.mem_append_left _ (by
      rw [List.getD_eq_getElem front 0 (by omega)]
      exact List.getElem_mem (by omega)))
    refine ⟨earlier, next, next + 1, front.length, hearlier, by omega, hnext, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      omega
    · rw [hfrontRead earlier (by omega), hfrontRead (next + 1) hnext]
      exact hnotminimum
    · rw [hfrontRead (next + 1) hnext, hfrontRead next (by omega)]
      exact hdescent
    · rw [hfrontRead next (by omega), hmaxRead]
      exact hnextMax

end D5.S3.Combinatorics.VincularStack.VincularStackMesh

namespace D5.S3.Combinatorics.VincularStack.VincularStackDetection

open VincularStackDefs VincularStackPatterns VincularStackMesh
open scoped List

theorem non_sortable_has_pattern (word : List ℕ) (hnodup : word.Nodup)
    (hbad : Contains231 (SC word)) : Contains1324 word ∨ ContainsMesh2413 word := by
  have hgeneral : ∀ size, ∀ current : List ℕ, current.length = size → current.Nodup →
      Contains231 (SC current) → Contains1324 current ∨ ContainsMesh2413 current := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
      intro current hsize hcurrent hbad
      by_cases hempty : current = []
      · subst current
        obtain ⟨earlier, middle, later, _, _, hlater, _⟩ := hbad
        simp [SC, Process] at hlater
      · obtain ⟨maximum, hmaximum⟩ := Option.isSome_iff_exists.mp
          (List.isSome_max?_of_ne_nil hempty)
        obtain ⟨hmaxmem, hmaxbound⟩ := List.max?_eq_some_iff.mp hmaximum
        obtain ⟨front, suffix, hsplit, _⟩ := List.eq_append_cons_of_mem hmaxmem
        subst current
        have hparentNodup : (front ++ suffix).Nodup :=
          ((List.Sublist.refl front).append (List.sublist_cons_self maximum suffix)).nodup
            hcurrent
        have hbound : ∀ value ∈ front ++ suffix, value < maximum := by
          intro value hvalue
          have hle : value ≤ maximum := by
            apply hmaxbound value
            rcases List.mem_append.mp hvalue with hfront | hsuffix
            · exact List.mem_append_left _ hfront
            · exact List.mem_append_right _ (List.mem_cons_of_mem maximum hsuffix)
          have hneq : value ≠ maximum := by
            intro heq
            subst value
            rcases List.mem_append.mp hvalue with hfront | hsuffix
            · exact (List.nodup_append.mp hcurrent).2.2 maximum hfront maximum
                List.mem_cons_self rfl
            · exact (List.nodup_cons.mp (List.nodup_append.mp hcurrent).2.1).1 hsuffix
          omega
        by_cases hparentBad : Contains231 (SC (front ++ suffix))
        · have hparentSize : (front ++ suffix).length < size := by
            simp only [List.length_append, List.length_cons] at hsize ⊢
            omega
          have hparent := inductionHypothesis (front ++ suffix).length hparentSize
            (front ++ suffix) rfl hparentNodup hparentBad
          let insertIndex (position : ℕ) :=
            if position < front.length then position else position + 1
          let eraseIndex (position : ℕ) :=
            if position < front.length then position else position - 1
          have hinsertRead : ∀ position < (front ++ suffix).length,
              (front ++ maximum :: suffix).getD (insertIndex position) 0 =
                (front ++ suffix).getD position 0 := by
            intro position hposition
            dsimp only [insertIndex]
            split_ifs with hfront
            · rw [List.getD_append front (maximum :: suffix) 0 position hfront,
                List.getD_append front suffix 0 position hfront]
            · rw [List.getD_append_right front (maximum :: suffix) 0 (position + 1)
                (by omega), List.getD_append_right front suffix 0 position (by omega)]
              have hoffset : position + 1 - front.length = position - front.length + 1 := by
                omega
              rw [hoffset, List.getD_cons_succ]
          have heraseRead : ∀ position < (front ++ maximum :: suffix).length,
              position ≠ front.length →
              (front ++ suffix).getD (eraseIndex position) 0 =
                (front ++ maximum :: suffix).getD position 0 := by
            intro position hposition hmarker
            dsimp only [eraseIndex]
            split_ifs with hfront
            · rw [List.getD_append front suffix 0 position hfront,
                List.getD_append front (maximum :: suffix) 0 position hfront]
            · rw [List.getD_append_right front suffix 0 (position - 1) (by omega),
                List.getD_append_right front (maximum :: suffix) 0 position (by omega)]
              have hoffset : position - front.length =
                  position - 1 - front.length + 1 := by omega
              rw [hoffset, List.getD_cons_succ]
          have hinsertLt : ∀ first second, first < second →
              insertIndex first < insertIndex second := by
            intro first second hlt
            dsimp only [insertIndex]
            split_ifs <;> omega
          have hinsertBound : ∀ position < (front ++ suffix).length,
              insertIndex position < (front ++ maximum :: suffix).length := by
            intro position hposition
            simp only [List.length_append, List.length_cons] at hposition ⊢
            dsimp only [insertIndex]
            split_ifs <;> omega
          rcases hparent with hclassical | hmesh
          · left
            obtain ⟨first, second, third, fourth, hfirst, hsecond, hthird, hfourth,
              hlow, hmiddle, hhigh⟩ := hclassical
            refine ⟨insertIndex first, insertIndex second, insertIndex third,
              insertIndex fourth, hinsertLt _ _ hfirst, hinsertLt _ _ hsecond,
              hinsertLt _ _ hthird, hinsertBound _ hfourth, ?_, ?_, ?_⟩
            · rw [hinsertRead first (by omega), hinsertRead third (by omega)]
              exact hlow
            · rw [hinsertRead third (by omega), hinsertRead second (by omega)]
              exact hmiddle
            · rw [hinsertRead second (by omega), hinsertRead fourth hfourth]
              exact hhigh
          · right
            obtain ⟨first, second, third, fourth, hfirst, hsecond, hthird, hfourth,
              hlow, hmiddle, hhigh, hbefore, hbetween⟩ := hmesh
            have hfirstMax : (front ++ suffix).getD first 0 < maximum := by
              apply hbound
              rw [List.getD_eq_getElem _ 0 (by omega)]
              exact List.getElem_mem (by omega)
            have hsecondMax : (front ++ suffix).getD second 0 < maximum := by
              apply hbound
              rw [List.getD_eq_getElem _ 0 (by omega)]
              exact List.getElem_mem (by omega)
            have hmaxRead : (front ++ maximum :: suffix).getD front.length 0 = maximum := by
              rw [List.getD_append_right front (maximum :: suffix) 0 front.length (by omega)]
              simp
            refine ⟨insertIndex first, insertIndex second, insertIndex third,
              insertIndex fourth, hinsertLt _ _ hfirst, hinsertLt _ _ hsecond,
              hinsertLt _ _ hthird, hinsertBound _ hfourth, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hinsertRead third (by omega), hinsertRead first (by omega)]
              exact hlow
            · rw [hinsertRead first (by omega), hinsertRead fourth hfourth]
              exact hmiddle
            · rw [hinsertRead fourth hfourth, hinsertRead second (by omega)]
              exact hhigh
            · intro position hposition
              rw [hinsertRead first (by omega)]
              by_cases hmarker : position = front.length
              · subst position
                rw [hmaxRead]
                exact le_of_lt hfirstMax
              · have hpositionBound : position < (front ++ maximum :: suffix).length :=
                  lt_trans hposition (hinsertBound second (by omega))
                rw [← heraseRead position hpositionBound hmarker]
                apply hbefore
                dsimp only [insertIndex, eraseIndex] at hposition ⊢
                split_ifs at hposition ⊢ <;> omega
            · intro position hleft hright
              rw [hinsertRead first (by omega), hinsertRead second (by omega)]
              by_cases hmarker : position = front.length
              · subst position
                rw [hmaxRead]
                rintro ⟨_, hless⟩
                omega
              · have hpositionBound : position < (front ++ maximum :: suffix).length :=
                  lt_trans hright (hinsertBound third (by omega))
                rw [← heraseRead position hpositionBound hmarker]
                apply hbetween
                · dsimp only [insertIndex, eraseIndex] at hleft ⊢
                  split_ifs at hleft ⊢ <;> omega
                · dsimp only [insertIndex, eraseIndex] at hright ⊢
                  split_ifs at hright ⊢ <;> omega
        · exact maximum_insertion_obstruction front suffix maximum hparentNodup hbound
            hparentBad hbad
  exact hgeneral word.length word rfl hnodup hbad

end D5.S3.Combinatorics.VincularStack.VincularStackDetection

namespace D5.S3.Combinatorics.VincularStack.VincularStackCharacterization

open VincularStackDefs VincularStackBasic VincularStackRun VincularStackMarkers
open VincularStackCuts VincularStackSites VincularStackPrefixes VincularStackPatterns
open VincularStackMesh VincularStackDetection VincularStackRestriction
open scoped List

theorem sortable_iff_avoids1324_and_mesh (word : List ℕ) (hnodup : word.Nodup) :
    ¬ Contains231 (SC word) ↔ ¬ Contains1324 word ∧ ¬ ContainsMesh2413 word := by
  constructor
  · intro havoid
    refine ⟨fun hpattern => havoid (contains1324_not_sortable word hnodup hpattern), ?_⟩
    rintro ⟨first, second, third, fourth, hfirst, hsecond, hthird, hfourth,
      hlow, hmiddle, hhigh, hbefore, hbetween⟩
    let minimum := word.getD first 0
    let maximum := word.getD second 0
    let tail := word.drop (second + 1)
    let front := (word.take second).filter (fun value => value ≤ maximum)
    let suffix := tail.filter (fun value => value ≤ maximum)
    have hprefixLength : (word.take second).length = second :=
      List.length_take_of_le (by omega)
    have hprefixMin : minimum ∈ word.take second := by
      have hfirstTake : first < (word.take second).length := by omega
      have hread : (word.take second)[first] = minimum := by
        rw [List.getElem_take]
        exact (List.getD_eq_getElem word 0 (by omega)).symm
      rw [← hread]
      exact List.getElem_mem hfirstTake
    have hminFront : minimum ∈ front := by
      apply List.mem_filter.mpr
      refine ⟨hprefixMin, ?_⟩
      simp only [decide_eq_true_eq]
      dsimp only [minimum, maximum]
      omega
    have hfrontBound : ∀ value ∈ front, minimum ≤ value := by
      intro value hvalue
      obtain ⟨position, hposition, hvalueRead⟩ :=
        List.mem_iff_getElem.mp (List.mem_filter.mp hvalue).1
      have hpositionBound : position < second := by omega
      have hread : (word.take second)[position] = word.getD position 0 := by
        rw [List.getElem_take, List.getD_eq_getElem word 0 (by omega)]
      rw [hread] at hvalueRead
      rw [← hvalueRead]
      exact hbefore position hpositionBound
    have hwordSplit : word = word.take second ++ maximum :: tail := by
      have hsplit := List.take_append_drop second word
      rw [List.drop_eq_getElem_cons (by omega : second < word.length)] at hsplit
      have hmaxRead : word[second] = maximum :=
        (List.getD_eq_getElem word 0 (by omega)).symm
      rw [hmaxRead] at hsplit
      exact hsplit.symm
    have hrestrictedSplit : word.filter (fun value => value ≤ maximum) =
        front ++ maximum :: suffix := by
      conv_lhs => rw [hwordSplit]
      simp [List.filter_append, front, suffix]
    have hwholeNodup : (front ++ maximum :: suffix).Nodup := by
      rw [← hrestrictedSplit]
      exact hnodup.filter _
    have hparentNodup : (front ++ suffix).Nodup :=
      ((List.Sublist.refl front).append (List.sublist_cons_self maximum suffix)).nodup
        hwholeNodup
    have hbound : ∀ value ∈ front ++ suffix, value < maximum := by
      intro value hvalue
      have hle : value ≤ maximum := by
        rcases List.mem_append.mp hvalue with hfront | hsuffix
        · exact of_decide_eq_true (List.mem_filter.mp hfront).2
        · exact of_decide_eq_true (List.mem_filter.mp hsuffix).2
      have hneq : value ≠ maximum := by
        intro heq
        subst value
        rcases List.mem_append.mp hvalue with hfront | hsuffix
        · exact (List.nodup_append.mp hwholeNodup).2.2 maximum hfront maximum
            List.mem_cons_self rfl
        · exact (List.nodup_cons.mp (List.nodup_append.mp hwholeNodup).2.1).1 hsuffix
      omega
    have hrestrictedAvoid : ¬ Contains231 (SC (front ++ maximum :: suffix)) := by
      rw [← hrestrictedSplit, restrict_sc word hnodup maximum]
      intro hpattern
      obtain ⟨embedding, hread⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (List.filter_sublist (p := fun value => value ≤ maximum) (l := SC word))
      obtain ⟨earlier, middle, later, hearlier, hmiddle, hlater, hsmall, hlarge⟩ := hpattern
      let earlierFin : Fin ((SC word).filter (fun value => value ≤ maximum)).length :=
        ⟨earlier, by omega⟩
      let middleFin : Fin ((SC word).filter (fun value => value ≤ maximum)).length :=
        ⟨middle, by omega⟩
      let laterFin : Fin ((SC word).filter (fun value => value ≤ maximum)).length :=
        ⟨later, hlater⟩
      have houtputRead (position : Fin ((SC word).filter
          (fun value => value ≤ maximum)).length) :
          (SC word).getD (embedding position).val 0 =
            ((SC word).filter (fun value => value ≤ maximum)).getD position.val 0 := by
        rw [List.getD_eq_getElem _ 0 (embedding position).isLt,
          List.getD_eq_getElem _ 0 position.isLt]
        exact (hread position).symm
      apply havoid
      refine ⟨(embedding earlierFin).val, (embedding middleFin).val,
        (embedding laterFin).val, embedding.strictMono hearlier,
        embedding.strictMono hmiddle, (embedding laterFin).isLt, ?_, ?_⟩
      · rw [houtputRead laterFin, houtputRead earlierFin]
        exact hsmall
      · rw [houtputRead earlierFin, houtputRead middleFin]
        exact hlarge
    have hnil : ¬ ContainsV [] := by
      rintro ⟨position, hposition, _⟩
      simp at hposition
    have hperm : (SC (front ++ suffix)).Perm (front ++ suffix) := by
      simpa [SC] using (process_preserves (front ++ suffix) [] hnil).1
    have hmarker := (maximum_insertion front suffix maximum hbound).1
    have hsplit := List.take_append_drop (outputGap front suffix) (SC (front ++ suffix))
    have hcut := (maximum_cut
      ((SC (front ++ suffix)).take (outputGap front suffix))
      ((SC (front ++ suffix)).drop (outputGap front suffix)) maximum
      (by rw [hsplit]; exact hperm.nodup_iff.mpr hparentNodup)
      (by rw [hsplit]; intro value hvalue; exact hbound value (hperm.mem_iff.mp hvalue))).mp
      (by rwa [← hmarker])
    have hfrontNonempty : front ≠ [] := by
      intro hempty
      simp [hempty] at hminFront
    have hgaple : outputGap front suffix ≤ (SC (front ++ suffix)).length := by
      rw [hperm.length_eq]
      exact le_of_lt ((maximum_insertion front suffix maximum hbound).2 hfrontNonempty)
    have hseparate : separatingCut (SC (front ++ suffix)) (outputGap front suffix) := by
      simpa only [hsplit, List.length_take, Nat.min_eq_left hgaple] using hcut.2
    have hsite := (separating_gap front suffix).mp hseparate |>.resolve_left hfrontNonempty
    have hempty : (snapshot front []).1 = [] := (no_pop_iff_records front).mpr hsite.1
    have hminimum := snapshot_minimum front [] minimum hnil
      (by simpa using hminFront) (by simpa using hfrontBound)
    have hstackPerm : (snapshot front []).2 |>.Perm front := by
      have hfrontPerm : (SC front).Perm front := by
        simpa [SC] using (process_preserves front [] hnil).1
      simpa only [SC, hminimum.2.2.2, hempty, List.nil_append] using hfrontPerm
    have hstackBound : ∀ value ∈ (snapshot front []).2, minimum ≤ value :=
      fun value hvalue => hfrontBound value (hstackPerm.mem_iff.mp hvalue)
    have htailRead (position : ℕ) (hposition : position < tail.length) :
        tail.getD position 0 = word.getD (second + 1 + position) 0 := by
      rw [List.getD_eq_getElem tail 0 hposition, List.getElem_drop,
        List.getD_eq_getElem word 0 (by
          have htailLength : tail.length = word.length - (second + 1) := List.length_drop
          omega)]
    have htailNe : ∀ value ∈ tail, value ≠ minimum ∧ value ≠ maximum := by
      have hsourceNodup : (word.take second ++ maximum :: tail).Nodup := by
        rwa [← hwordSplit]
      intro value hvalue
      refine ⟨?_, ?_⟩
      · intro heq
        exact (List.nodup_append.mp hsourceNodup).2.2 minimum hprefixMin value
          (List.mem_cons_of_mem maximum hvalue) heq.symm
      · intro heq
        subst value
        exact (List.nodup_cons.mp (List.nodup_append.mp hsourceNodup).2.1).1 hvalue
    let offset := third - (second + 1)
    have hoffset : offset < tail.length := by
      simp only [tail, List.length_drop]
      dsimp only [offset]
      omega
    have hinputIndex : second + 1 + offset = third := by dsimp [offset]; omega
    have hxRead : tail.getD offset 0 = word.getD third 0 := by
      rw [htailRead offset hoffset, hinputIndex]
    have hsmallBefore : ∀ value ∈ tail.take offset, value ≤ maximum → value < minimum := by
      intro value hvalue hvalueMax
      obtain ⟨position, hposition, hread⟩ := List.mem_iff_getElem.mp hvalue
      have hpositionOffset : position < offset := by
        simp only [List.length_take] at hposition
        omega
      have hpositionTail : position < tail.length := by omega
      have hpositionRead : word.getD (second + 1 + position) 0 = value := by
        rw [← htailRead position hpositionTail, List.getD_eq_getElem tail 0 hpositionTail]
        rw [List.getElem_take] at hread
        exact hread
      have hne := htailNe value ((List.take_sublist offset tail).subset hvalue)
      have hregion := hbetween (second + 1 + position) (by omega) (by omega)
      rw [hpositionRead] at hregion
      dsimp only [minimum, maximum] at hvalueMax ⊢
      dsimp only [minimum, maximum] at hne
      omega
    have htailSplit : tail = tail.take offset ++
        word.getD third 0 :: tail.drop (offset + 1) := by
      have hsplit := List.take_append_drop offset tail
      rw [List.drop_eq_getElem_cons hoffset] at hsplit
      have hentryRead : tail[offset] = word.getD third 0 := by
        rw [← List.getD_eq_getElem tail 0 hoffset]
        exact hxRead
      rw [hentryRead] at hsplit
      exact hsplit.symm
    have hsuffixSplit : suffix = (tail.take offset).filter (fun value => value ≤ maximum) ++
        word.getD third 0 :: (tail.drop (offset + 1)).filter (fun value => value ≤ maximum) := by
      dsimp only [suffix]
      conv_lhs => rw [htailSplit]
      rw [List.filter_append, List.filter_cons_of_pos (by
        simp only [decide_eq_true_eq]
        dsimp only [maximum]
        omega)]
    have hheadSmall : ∃ entry rest, suffix = entry :: rest ∧ entry < minimum := by
      cases hfiltered : (tail.take offset).filter (fun value => value ≤ maximum) with
      | nil =>
        refine ⟨word.getD third 0,
          (tail.drop (offset + 1)).filter (fun value => value ≤ maximum), ?_, hlow⟩
        simpa only [hfiltered, List.nil_append] using hsuffixSplit
      | cons entry rest =>
        refine ⟨entry, rest ++ word.getD third 0 ::
          (tail.drop (offset + 1)).filter (fun value => value ≤ maximum), ?_, ?_⟩
        · simpa only [hfiltered, List.cons_append] using hsuffixSplit
        · have hentry : entry ∈ (tail.take offset).filter (fun value => value ≤ maximum) := by
            simp [hfiltered]
          exact hsmallBefore entry (List.mem_filter.mp hentry).1
            (of_decide_eq_true (List.mem_filter.mp hentry).2)
    obtain ⟨entry, rest, hsuffix, hentry⟩ := hheadSmall
    have htemporary : ¬ ∃ lower ∈ (snapshot front []).2, lower < entry := by
      rintro ⟨lower, hlower, hless⟩
      have := hstackBound lower hlower
      omega
    have hrelation : ∀ left ∈ suffix, ∀ right ∈ front, left < right := by
      have hcondition := hsite.2
      rw [hsuffix] at hcondition
      rw [hsuffix]
      exact (hcondition.resolve_left htemporary)
    have hupperTail : word.getD fourth 0 ∈ tail := by
      let position := fourth - (second + 1)
      have hposition : position < tail.length := by
        simp only [tail, List.length_drop]
        dsimp only [position]
        omega
      have hindex : second + 1 + position = fourth := by dsimp [position]; omega
      rw [← hindex, ← htailRead position hposition, List.getD_eq_getElem tail 0 hposition]
      exact List.getElem_mem hposition
    have hupperSuffix : word.getD fourth 0 ∈ suffix := by
      apply List.mem_filter.mpr
      refine ⟨hupperTail, ?_⟩
      simp only [decide_eq_true_eq]
      exact le_of_lt hhigh
    have := hrelation (word.getD fourth 0) hupperSuffix minimum hminFront
    omega
  · rintro ⟨hclassical, hmesh⟩ hbad
    exact (non_sortable_has_pattern word hnodup hbad).elim hclassical hmesh

end D5.S3.Combinatorics.VincularStack.VincularStackCharacterization
