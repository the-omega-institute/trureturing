/- GID: D5/S3/Combinatorics/PopStack/PopStackInflation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackInflation
   mirror-E: none(waiver:ascending-inflation-pattern-obstruction)
   anchors: []
   utility: none
   digest: Ascending early-entry inflations of simple permutations contain 2341. -/

import D5.S3.Combinatorics.PopStack.PopStackDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackInflation

open PopStackDefs

def inflate (permutation : List ℕ) (index : ℕ) (block : List ℕ) : List ℕ :=
  let pivot := permutation.getD index 0
  let shift := fun value => if pivot < value then value + block.length - 1 else value
  (permutation.take index).map shift ++ block.map (fun value => pivot + value - 1) ++
    (permutation.drop (index + 1)).map shift

theorem ascending_first_inflation (first : ℕ) (tail block : List ℕ)
    (hperm : (first :: tail).Perm (List.range' 1 (tail.length + 1)))
    (hsimple : IsSimple (first :: tail)) (hlen : 3 ≤ tail.length + 1)
    (hblock : block.Perm (List.range' 1 block.length)) (hascent : Occurs [1, 2] block) :
    Occurs [2, 3, 4, 1] (inflate (first :: tail) 0 block) := by
  have hfirst : 1 < first ∧ first < tail.length + 1 := by
    have hmem : first ∈ List.range' 1 (tail.length + 1) := hperm.mem_iff.mp (by simp)
    have hb := List.mem_range'_1.mp hmem
    have hmin : first ≠ 1 := by
      intro heq
      subst first
      have hrange : List.range' 1 (tail.length + 1) = 1 :: List.range' 2 tail.length :=
        by rw [List.range'_succ]
      rw [hrange] at hperm
      have hh := hsimple 1 tail.length 2 (by omega) (by simp) (by simp; omega)
      simp only [List.drop_succ_cons, List.drop_zero, List.take_length] at hh
      exact hh hperm.cons_inv
    have hmax : first ≠ tail.length + 1 := by
      intro heq
      have hrange : (List.range' 1 (tail.length + 1)).Perm
          ((tail.length + 1) :: List.range' 1 tail.length) := by
        rw [List.range'_1_concat]
        simpa only [Nat.add_comm] using
          List.perm_append_singleton (1 + tail.length) (List.range' 1 tail.length)
      have hrest := (hperm.trans hrange)
      rw [heq] at hrest
      have hh := hsimple 1 tail.length 1 (by omega) (by simp) (by simp; omega)
      simp only [List.drop_succ_cons, List.drop_zero, List.take_length] at hh
      exact hh hrest.cons_inv
    constructor <;> omega
  have hcut : ∃ lower upper, lower < first ∧ first < upper ∧
      [upper, lower].Sublist tail := by
    by_contra hnone
    have hforbid : ∀ lower upper, lower < first → first < upper →
        ¬ [upper, lower].Sublist tail := by
      intro lower upper hlower hupper hsub
      exact hnone ⟨lower, upper, hlower, hupper, hsub⟩
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1 (by omega))
    have hdistinct : ∀ value ∈ tail, value ≠ first := by
      intro value hvalue heq
      exact (List.nodup_cons.mp hnodup).1 (heq ▸ hvalue)
    have separate : ∀ remaining : List ℕ, (∀ value ∈ remaining, value ≠ first) →
        (∀ lower upper, lower < first → first < upper →
          ¬ [upper, lower].Sublist remaining) →
        ∃ left right, remaining = left ++ right ∧
          (∀ value ∈ left, value < first) ∧ (∀ value ∈ right, first < value) := by
      intro remaining
      induction remaining with
      | nil => intro _ _; exact ⟨[], [], rfl, by simp⟩
      | cons value remaining ih =>
        intro hne hno
        by_cases hlower : value < first
        · obtain ⟨left, right, heq, hleft, hright⟩ := ih
            (fun other hother => hne other (List.mem_cons_of_mem value hother))
            (fun lower upper hlow hupp hsub =>
              hno lower upper hlow hupp (hsub.cons value))
          refine ⟨value :: left, right, by simp [heq], ?_, hright⟩
          intro other hother
          rcases List.mem_cons.mp hother with rfl | hother
          · exact hlower
          · exact hleft other hother
        · have hupper : first < value := by have hh := hne value (by simp); omega
          refine ⟨[], value :: remaining, rfl, by simp, ?_⟩
          intro other hother
          rcases List.mem_cons.mp hother with rfl | hother
          · exact hupper
          · have hh := hne other (List.mem_cons_of_mem value hother)
            by_contra hnotupper
            have hsmall : other < first := by omega
            have hsub : [value, other].Sublist (value :: remaining) :=
              (List.singleton_sublist.mpr hother).cons_cons value
            exact hno other value hsmall hupper hsub
    obtain ⟨left, right, heq, hleft, hright⟩ := separate tail hdistinct hforbid
    have hprefix : (first :: left).Sublist (first :: tail) := by
      rw [heq]
      exact (List.sublist_append_left left right).cons_cons first
    have hprefperm : (first :: left).Perm (List.range' 1 first) := by
      apply (List.perm_ext_iff_of_nodup (hnodup.sublist hprefix)
        (List.nodup_range' 1 (by omega))).mpr
      intro value
      constructor
      · intro hvalue
        have hwhole := hperm.mem_iff.mp (hprefix.subset hvalue)
        have hlow := (List.mem_range'_1.mp hwhole).1
        have hhigh : value ≤ first := by
          rcases List.mem_cons.mp hvalue with rfl | hvalue
          · exact le_rfl
          · have hh := hleft value hvalue; omega
        exact List.mem_range'_1.mpr ⟨hlow, by omega⟩
      · intro hvalue
        obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hvalue
        by_cases hsame : value = first
        · simp [hsame]
        · have hwhole : value ∈ first :: tail :=
            hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hlow, by omega⟩)
          have htail : value ∈ tail := (List.mem_cons.mp hwhole).resolve_left hsame
          rw [heq, List.mem_append] at htail
          rcases htail with htail | htail
          · exact List.mem_cons_of_mem first htail
          · have hh := hright value htail; omega
    have hprefsize : (first :: left).length = first := by
      simpa only [List.length_range'] using hprefperm.length_eq
    have hslice : (first :: tail).take first = first :: left := by
      rw [heq, ← List.cons_append, ← hprefsize]
      simp
    have hh := hsimple 0 first 1 (by omega) (by simp; omega) (by simp; omega)
    simp only [List.drop_zero, hslice] at hh
    exact hh hprefperm
  obtain ⟨lower, upper, hlower, hupper, hpair⟩ := hcut
  obtain ⟨values, hinc, hmem, hsub, _⟩ := hascent
  have hsmall : values 1 < values 2 := hinc 1 (by omega) (by simp)
  have hlowbound := List.mem_range'_1.mp (hblock.mem_iff.mp (hmem 1 (by omega) (by simp)))
  have hhighbound := List.mem_range'_1.mp (hblock.mem_iff.mp (hmem 2 (by omega) (by simp)))
  let shift := fun value => if first < value then value + block.length - 1 else value
  let witness := fun rank : ℕ => match rank with
    | 1 => lower
    | 2 => first + values 1 - 1
    | 3 => first + values 2 - 1
    | 4 => upper + block.length - 1
    | _ => 0
  have hselected :
      [first + values 1 - 1, first + values 2 - 1,
        upper + block.length - 1, lower].Sublist
      (block.map (fun value => first + value - 1) ++ tail.map shift) := by
    have hblocksub := hsub.map (fun value => first + value - 1)
    have htailsub := hpair.map shift
    have huppernot : ¬ first < lower := by omega
    simp only [List.map_cons, List.map_nil, shift, if_pos hupper,
      if_neg huppernot] at htailsub
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      hblocksub.append htailsub
  have hinflated : inflate (first :: tail) 0 block =
      block.map (fun value => first + value - 1) ++ tail.map shift := by
    simp [inflate, shift]
  rw [hinflated]
  refine ⟨witness, ?_, ?_, ?_, by simp⟩
  · intro rank hrank hbound
    have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp at hbound; omega
    rcases hcases with rfl | rfl | rfl <;> simp only [witness, Nat.reduceAdd] <;> omega
  · intro rank hrank hbound
    have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
      simp at hbound; omega
    have hsubset := hselected.subset
    rcases hcases with rfl | rfl | rfl | rfl <;> apply hsubset <;> simp [witness]
  · simpa only [List.map_cons, List.map_nil, witness] using hselected

theorem ascending_second_inflation (first second : ℕ) (tail block : List ℕ)
    (hperm : (first :: second :: tail).Perm (List.range' 1 (tail.length + 2)))
    (hsimple : IsSimple (first :: second :: tail)) (hlen : 2 ≤ tail.length)
    (hsecondne : second ≠ 1) (hblock : block.Perm (List.range' 1 block.length))
    (hascent : Occurs [1, 2] block) :
    Occurs [2, 3, 4, 1] (inflate (first :: second :: tail) 1 block) := by
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1 (by omega))
  have hfirstne : first ≠ 1 := by
    intro heq
    subst first
    have hrange : List.range' 1 (tail.length + 2) =
        1 :: List.range' 2 (tail.length + 1) := by rw [List.range'_succ]
    rw [hrange] at hperm
    have hrest := hperm.cons_inv
    have hinterval := hsimple 1 (tail.length + 1) 2 (by omega)
      (by simp) (by simp; omega)
    have hslice : ((1 :: second :: tail).drop 1).take (tail.length + 1) =
        second :: tail := by simp
    rw [hslice] at hinterval
    exact hinterval hrest
  have hfirstbound := List.mem_range'_1.mp (hperm.mem_iff.mp (by simp :
    first ∈ first :: second :: tail))
  have hsecondbound := List.mem_range'_1.mp (hperm.mem_iff.mp (by simp :
    second ∈ first :: second :: tail))
  have hfirstsecondne : first ≠ second := by
    intro heq
    exact (List.nodup_cons.mp hnodup).1 (by simp [heq])
  obtain ⟨values, hinc, hmem, hsub, _⟩ := hascent
  have hsmall : values 1 < values 2 := hinc 1 (by omega) (by simp)
  have hlowbound := List.mem_range'_1.mp (hblock.mem_iff.mp (hmem 1 (by omega) (by simp)))
  have hhighbound := List.mem_range'_1.mp (hblock.mem_iff.mp (hmem 2 (by omega) (by simp)))
  let shift := fun value => if second < value then value + block.length - 1 else value
  have hinflated : inflate (first :: second :: tail) 1 block =
      shift first :: (block.map (fun value => second + value - 1) ++ tail.map shift) := by
    simp [inflate, shift]
  rw [hinflated]
  by_cases hfirstsmall : first < second
  · have honetail : 1 ∈ tail := by
      have hone := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr (show 1 ≤ 1 ∧ 1 < 1 + (tail.length + 2) by omega))
      simpa only [List.mem_cons, eq_comm, hfirstne, hsecondne, false_or] using hone
    have hshiftfirst : shift first = first := by simp [shift, show ¬ second < first by omega]
    have hshiftone : shift 1 = 1 := by simp [shift, show ¬ second < 1 by omega]
    let witness := fun rank : ℕ => match rank with
      | 1 => 1
      | 2 => first
      | 3 => second + values 1 - 1
      | 4 => second + values 2 - 1
      | _ => 0
    have hselected : [first, second + values 1 - 1, second + values 2 - 1, 1].Sublist
        (shift first :: (block.map (fun value => second + value - 1) ++ tail.map shift)) := by
      have hblocksub := hsub.map (fun value => second + value - 1)
      have htailsub := (List.singleton_sublist.mpr honetail).map shift
      rw [hshiftfirst]
      apply List.Sublist.cons_cons
      simpa only [List.map_cons, List.map_nil, hshiftone, List.cons_append,
        List.nil_append] using hblocksub.append htailsub
    refine ⟨witness, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hbound
      have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp at hbound; omega
      rcases hcases with rfl | rfl | rfl <;> simp only [witness, Nat.reduceAdd] <;> omega
    · intro rank hrank hbound
      have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
        simp at hbound; omega
      rcases hcases with rfl | rfl | rfl | rfl <;> apply hselected.subset <;> simp [witness]
    · simpa only [List.map_cons, List.map_nil, witness] using hselected
  · have hfirstlarge : second < first := by omega
    have hcut : ∃ lower upper, lower < second ∧ second < upper ∧
        [upper, lower].Sublist tail := by
      by_contra hnone
      have hforbid : ∀ lower upper, lower < second → second < upper →
          ¬ [upper, lower].Sublist tail := by
        intro lower upper hlower hupper hsublist
        exact hnone ⟨lower, upper, hlower, hupper, hsublist⟩
      have htailnodup := (List.nodup_cons.mp hnodup).2
      have hdistinct : ∀ value ∈ tail, value ≠ second := by
        intro value hvalue heq
        exact (List.nodup_cons.mp htailnodup).1 (heq ▸ hvalue)
      have separate : ∀ remaining : List ℕ, (∀ value ∈ remaining, value ≠ second) →
          (∀ lower upper, lower < second → second < upper →
            ¬ [upper, lower].Sublist remaining) →
          ∃ left right, remaining = left ++ right ∧
            (∀ value ∈ left, value < second) ∧ (∀ value ∈ right, second < value) := by
        intro remaining
        induction remaining with
        | nil => intro _ _; exact ⟨[], [], rfl, by simp⟩
        | cons value remaining ih =>
          intro hne hno
          by_cases hlower : value < second
          · obtain ⟨left, right, heq, hleft, hright⟩ := ih
              (fun other hother => hne other (List.mem_cons_of_mem value hother))
              (fun lower upper hlow hupp hsublist =>
                hno lower upper hlow hupp (hsublist.cons value))
            refine ⟨value :: left, right, by simp [heq], ?_, hright⟩
            intro other hother
            rcases List.mem_cons.mp hother with rfl | hother
            · exact hlower
            · exact hleft other hother
          · have hupper : second < value := by have hh := hne value (by simp); omega
            refine ⟨[], value :: remaining, rfl, by simp, ?_⟩
            intro other hother
            rcases List.mem_cons.mp hother with rfl | hother
            · exact hupper
            · have hh := hne other (List.mem_cons_of_mem value hother)
              by_contra hnotupper
              have hsmallother : other < second := by omega
              have hsublist : [value, other].Sublist (value :: remaining) :=
                (List.singleton_sublist.mpr hother).cons_cons value
              exact hno other value hsmallother hupper hsublist
      obtain ⟨left, right, heq, hleft, hright⟩ := separate tail hdistinct hforbid
      have hprefix : (second :: left).Sublist (second :: tail) := by
        rw [heq]
        exact (List.sublist_append_left left right).cons_cons second
      have hprefperm : (second :: left).Perm (List.range' 1 second) := by
        apply (List.perm_ext_iff_of_nodup (htailnodup.sublist hprefix)
          (List.nodup_range' 1 (by omega))).mpr
        intro value
        constructor
        · intro hvalue
          have hwhole := hperm.mem_iff.mp
            (List.mem_cons_of_mem first (hprefix.subset hvalue))
          have hlow := (List.mem_range'_1.mp hwhole).1
          have hhigh : value ≤ second := by
            rcases List.mem_cons.mp hvalue with rfl | hvalue
            · exact le_rfl
            · have hh := hleft value hvalue; omega
          exact List.mem_range'_1.mpr ⟨hlow, by omega⟩
        · intro hvalue
          obtain ⟨hlow, hhigh⟩ := List.mem_range'_1.mp hvalue
          by_cases hsame : value = second
          · simp [hsame]
          · have hwhole : value ∈ first :: second :: tail :=
              hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hlow, by omega⟩)
            have hvaluefirst : value ≠ first := by omega
            have htail := (List.mem_cons.mp
              ((List.mem_cons.mp hwhole).resolve_left hvaluefirst)).resolve_left hsame
            rw [heq, List.mem_append] at htail
            rcases htail with htail | htail
            · exact List.mem_cons_of_mem second htail
            · have hh := hright value htail; omega
      have hprefsize : (second :: left).length = second := by
        simpa only [List.length_range'] using hprefperm.length_eq
      have hslice : (second :: tail).take second = second :: left := by
        rw [heq, ← List.cons_append, ← hprefsize]
        simp
      have hinterval := hsimple 1 second 1 (by omega) (by simp; omega) (by simp; omega)
      simp only [List.drop_succ_cons, List.drop_zero, hslice] at hinterval
      exact hinterval hprefperm
    obtain ⟨lower, upper, hlower, hupper, hpair⟩ := hcut
    let witness := fun rank : ℕ => match rank with
      | 1 => lower
      | 2 => second + values 1 - 1
      | 3 => second + values 2 - 1
      | 4 => upper + block.length - 1
      | _ => 0
    have hselected :
        [second + values 1 - 1, second + values 2 - 1,
          upper + block.length - 1, lower].Sublist
        (block.map (fun value => second + value - 1) ++ tail.map shift) := by
      have hblocksub := hsub.map (fun value => second + value - 1)
      have htailsub := hpair.map shift
      simp only [List.map_cons, List.map_nil, shift, if_pos hupper,
        if_neg (show ¬ second < lower by omega)] at htailsub
      simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
        hblocksub.append htailsub
    have hselectedfull := hselected.cons (shift first)
    refine ⟨witness, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hbound
      have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp at hbound; omega
      rcases hcases with rfl | rfl | rfl <;> simp only [witness, Nat.reduceAdd] <;> omega
    · intro rank hrank hbound
      have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
        simp at hbound; omega
      rcases hcases with rfl | rfl | rfl | rfl <;>
        apply hselectedfull.subset <;> simp [witness]
    · simpa only [List.map_cons, List.map_nil, witness] using hselectedfull

end D5.S3.Combinatorics.PopStack.PopStackInflation
